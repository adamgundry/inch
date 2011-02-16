> {-# LANGUAGE GADTs, TypeOperators #-}

> module TypeCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Bitraversable

> import BwdFwd
> import TyNum
> import Type
> import Num
> import Syntax
> import Context
> import Unify
> import Orphans
> import Kit
> import Error
> import PrettyPrinter


> inferKind :: Bwd (TyName ::: Kind) -> Ty String -> Contextual t (Type ::: Kind)
> inferKind g (TyVar a)    = (\ (b ::: k) -> TyVar b ::: k) <$> lookupTyVar g a
> inferKind g (TyCon c)    = (TyCon c :::) <$> lookupTyCon c
> inferKind g (TyApp f s)  = do
>     f' ::: k  <- inferKind g f
>     case k of
>         KindArr k1 k2 -> do
>             s' ::: l  <- inferKind g s
>             unless (k1 == l) $ errKindMismatch (s' ::: l) k1
>             return $ TyApp f' s' ::: k2
>         _ -> errKindNotArrow k
> inferKind g Arr             = return $ Arr ::: Set ---> Set ---> Set
> inferKind g (TyNum n)       = (\ n -> TyNum n ::: KindNum) <$> checkNumKind g n
> inferKind g (Bind b a k t)  = do
>     n <- freshName
>     ty ::: l <- inferKind (g :< ((a, n) ::: k)) (unbind a t)
>     return $ Bind b a k (bind (a, n) ty) ::: l
> inferKind g (Qual p t) = do
>     p' <- checkPredKind g p
>     t' ::: k <- inferKind g t
>     return (Qual p' t' ::: k)

> checkNumKind :: Bwd (TyName ::: Kind) -> TyNum String -> Contextual t TypeNum
> checkNumKind g (NumConst k) = return $ NumConst k
> checkNumKind g (NumVar a) = lookupNumVar g a
> checkNumKind g (m :+: n) = (:+:) <$> checkNumKind g m <*> checkNumKind g n
> checkNumKind g (Neg n) = Neg <$> checkNumKind g n

> checkPredKind :: Bwd (TyName ::: Kind) -> Pred String -> Contextual t Predicate
> checkPredKind g (n :<=: m) = (:<=:) <$> checkNumKind g n <*> checkNumKind g m


> goLam :: Type -> Contextual Term ()
> goLam tau = modify $ \ st@(St{tValue = Lam x t}) ->
>     st {  tValue = unbind x t
>        ,  context = context st :< Layer (LamBody (x ::: tau) ())
>        }


|goAppLeft| descends left into an application.

> goAppLeft :: Contextual Term ()
> goAppLeft = modify $ \ st@(St{tValue = TmApp f s}) ->
>     st {tValue = f, context = context st :< Layer (AppLeft () s)}



> goAnnotLeft :: Contextual Term ()
> goAnnotLeft = modify $ \ st@(St{tValue = t :? ty}) ->
>     st {tValue = t, context = context st :< Layer (AnnotLeft () ty)}



|goUp tau acc| is called when the term at the current location has
been given type |tau|, and it proceeds up and then right to find
the next type inference problem.

The accumulator |acc| collects variable definitions that |tau| may depend
on, and hence must be reinserted into the context once the new location
is found.

> goUp :: Type -> Suffix -> ContextualWriter [Predicate] Term Type
> goUp tau _Xi = do
>     st@(St{tValue = t}) <- lift get
>     case context st of
>       (es :< Layer l) ->
>         case l of         
>             AppLeft () a -> do
>                 lift $ put st{tValue = a,
>                     context = es <>< _Xi :< Layer (AppRight (t ::: tau) ())}
>                 inferType
>             AppRight (f ::: sigma) () -> do
>                 lift $ put st{tValue = TmApp f t, context = es <>< _Xi}
>                 tau' <- lift $ matchAppTypes sigma tau
>                 goUp tau' F0
>             LamBody (x ::: sigma) () -> do
>                 lift $ put st{tValue = Lam x (bind x t), context = es}
>                 goUp (sigma --> tau) _Xi
>             AnnotLeft () ty -> do
>                 lift $ put st{tValue = t :? ty, context = es <>< _Xi}
>                 lift $ unify ty tau
>                 goUp ty F0
>             PatternTop _ _ -> do
>                 lift $ put st{context = es <>< _Xi}
>                 return tau
>       (es :< A e) -> do
>           lift $ put st{context = es}
>           goUp tau (e :> _Xi)
>       B0 -> error (  "Ran out of context when going up from " 
>                      ++ (show t) ++ " : " ++ (show tau))


|matchAppTypes sigma tau| determines the return type of a function
whose overall type is $\sigma$ and whose argument type is $\tau$. It
unifies $\sigma$ with $\tau \rightarrow \alpha$, where $\alpha$
is a fresh variable, then returns $\alpha$.

> matchAppTypes :: Type -> Type -> Contextual t Type
> matchAppTypes sigma tau = do
>     alpha <- fresh "_t" (Hole ::: Set)
>     unify sigma (tau --> TyVar alpha)
>     return $ TyVar alpha


> specialise :: Type -> Contextual t Type
> specialise (TyApp f s)     = TyApp f <$> specialise s
> specialise (Bind b x k t)  = do
>     beta <- fresh x (Fixed ::: k)
>     specialise (unbind beta t)
> specialise (Qual p t)      = modifyContext (:< Constraint p) >> specialise t
> specialise t               = return t

> instantiate :: Type -> Contextual t (Type, [Predicate])
> instantiate t = runWriterT (spec t)
>   where
>     spec :: Type -> ContextualWriter [Predicate] t Type
>     spec (TyApp f s)     = TyApp f <$> spec s
>     spec (Bind b x k t)  = do
>         beta <- lift $ fresh x (Hole ::: k)
>         spec (unbind beta t)
>     spec (Qual p t)      = tell [p] >> spec t
>     spec t               = return t


> solvePred :: Bool -> Predicate -> Contextual t Bool
> solvePred try p = getContext >>= solvePredIn try p

> solvePredIn :: Bool -> Predicate -> Context -> Contextual t Bool
> solvePredIn try p g = do
>     -- mtrace $ "Solving " ++ show (bindPred (toNum . seekTy g) p) ++ "\nin " ++ show (normaliseContext g)
>     m <- normalisePred p
>     seekTruth g [] m
>   where
>     seekTruth :: Context -> [NormalNum] -> NormalNum -> Contextual t Bool
>     seekTruth B0 ns m = deduce m ns
>     seekTruth (g :< Constraint q) ns m = do
>         n <- normalisePred q
>         seekTruth g (n:ns) m             
>     seekTruth (g :< A (a := Some d ::: KindNum)) ns m = do
>         dn <- typeToNum d
>         seekTruth g (map (substNum a dn) ns) (substNum a dn m)
>     seekTruth (g :< A (a := _ ::: KindNum)) ns m = case lookupVariable a m of
>         Just _   -> deduce m ns
>         Nothing  -> seekTruth g ns m
>     seekTruth (g :< _) ns m = seekTruth g ns m

>     deduce :: NormalNum -> [NormalNum] -> Contextual t Bool
>     deduce m ns | Just k <- getConstant m =
>         if k >= 0  then  return True
>                    else  fail $ "Impossible constraint 0 <= " ++ show k
>     deduce m ns | m `elem` ns  = return True
>                 | try          = return False
>                 | otherwise    = fail $
>       "Could not solve constraint 0 <= " ++ show (prettyFst (simplifyNum $ reifyNum m))

> solvePreds try = mapM (solvePred try)

> expandPred :: Predicate -> Contextual t Predicate
> expandPred p = (\ g -> bindPred (toNum . seekTy g) p) <$> getContext

> generalise :: Type -> Contextual t Type
> generalise t = do
>     g <- getContext
>     (g', t') <- help g t
>     putContext g'
>     return t'
>   where
>     help (g :< Layer FunTop) t                  = return (g, t)
>     help (g :< A (((a, n) := Some d ::: k))) t  = help g (subst (a, n) d t)
>     help (g :< A (((a, n) := _ ::: k))) t       = help g (Bind All a k (bind (a, n) t))
>     help (g :< Constraint p) t                  = do
>         b <- solvePredIn True p g
>         if b then help g t else help g (Qual p t)



> inferType :: ContextualWriter [Predicate] Term Type
> inferType = lift getT >>= \ t -> case t of
>     TmVar x -> do
>         (_ ::: sc) <- lift $ lookupTmVar x
>         (ty, cs) <- lift $ instantiate sc
>         tell cs
>         goUp ty F0
>     TmCon c -> do
>         sc <- lift $ lookupTmCon c
>         (ty, cs) <- lift $ instantiate sc
>         tell cs
>         goUp ty F0
>     TmApp f s -> lift goAppLeft >> inferType
>     Lam x t -> do
>         a <- lift $ fresh "a" (Hole ::: Set)
>         lift $ goLam (TyVar a)
>         inferType
>     t :? ty -> lift goAnnotLeft >> inferType


> infer :: Tm String String -> Contextual () (Term ::: Type, [Predicate])
> infer t = inLocation ("in expression " ++ show (prettyHigh t)) $ do
>     t' <- scopeCheckTypes t
>     (ty, cs) <- withT t' $ runWriterT inferType
>     return (t' ::: ty, cs)

> scopeCheckTypes :: Tm String String -> Contextual () Term
> scopeCheckTypes = traverseTypes (\ t -> tmOf <$> inferKind B0 t)




> typeCheck p = runStateT (checkProg p) initialState

> checkProg :: Prog String String -> Contextual () Program
> checkProg = mapM checkDecl 

> checkDecl :: Decl String String -> Contextual () Declaration
> checkDecl (DD d) = DD <$> checkDataDecl d
> checkDecl (FD f) = FD <$> checkFunDecl f
>     

> checkDataDecl :: DataDecl String String -> Contextual () DataDeclaration
> checkDataDecl (DataDecl t k cs) = inLocation ("in data type " ++ t) $ do
>     unless (targetsSet k) $ errKindTarget k
>     insertTyCon t k
>     DataDecl t k <$> mapM (checkConstructor t) cs

> checkConstructor :: TyConName -> Con String -> Contextual () Constructor
> checkConstructor t (c ::: ty) = inLocation ("in constructor " ++ c) $ do
>     (ty' ::: k) <- inferKind B0 ty
>     unless (k == Set) $ errKindNotSet k
>     unless (ty' `targets` t) $ errConstructorTarget ty'
>     insertTmCon c ty'
>     return (c ::: ty')

> checkFunDecl :: FunDecl String String -> Contextual () FunDeclaration
> checkFunDecl (FunDecl s Nothing pats@(Pat xs _ _ : _)) =
>   inLocation ("in declaration of " ++ s) $ do
>     modifyContext (:< Layer FunTop)
>     sty     <- TyVar <$> fresh "sty" (Hole ::: Set)
>     (pattys, cs)  <- unzip <$> mapM (checkPat (s ::: sty)) pats
>     modifyContext (<><< map Constraint (concat cs))
>     ty'     <- simplifyTy <$> generalise sty
>     modifyContext (:< Func s ty')
>     return $ FunDecl s (Just ty') (map tmOf pattys)
> checkFunDecl (FunDecl s (Just st) pats@(Pat xs _ _ : _)) = 
>   inLocation ("in declaration of " ++ s) $ do
>     modifyContext (:< Layer FunTop)
>     sty ::: k <- inLocation ("in type " ++ show (prettyHigh st)) $ inferKind B0 st
>     unless (k == Set) $ errKindNotSet k
>     (pattys, cs) <- unzip <$> mapM (checkPat (s ::: sty)) pats
>     let ty = tyOf (head pattys)
>     modifyContext (<><< map Constraint (concat cs))
>     ty' <- simplifyTy <$> generalise ty
>     (ty'', cs') <- instantiate ty'
>     sty' <- specialise sty
>     inLocation ("when matching inferred type\n        " ++ show (prettyFst ty')
>         ++ "\n    against given type\n        " ++ show (prettyFst sty)) $
>             unify ty'' sty'
>     solvePreds False cs'
>     modifyContext (:< Func s ty')
>     return (FunDecl s (Just sty) (map tmOf pattys))
> checkFunDecl (FunDecl s _ []) =
>   inLocation ("in declaration of " ++ s) $ fail $ "No alternative"



> checkPat :: String ::: Type -> Pat String String ->
>     Contextual () (Pattern ::: Type, [Predicate])
> checkPat (s ::: sty) (Pat xs g t) =
>   inLocation ("in alternative " ++ s ++ " " ++ show (prettyHigh (Pat xs g t))) $ do
>     (ps, btys, cs) <- checkPatTerms xs
>     modifyContext (:< Layer (PatternTop (s ::: sty) btys))
>     (t' ::: ty, cs') <- infer t
>     let g' = Trivial -- nonsense
>     let oty = foldr (-->) ty (map tyOf ps)
>     (sty', cs'') <- instantiate sty
>     unify oty sty'
>     return (Pat (fmap tmOf ps) g' t' ::: oty, cs ++ cs' ++ cs'')

> checkPatTerms :: [PatTerm String String] ->
>     Contextual () ([PatternTerm ::: Type], [TmName ::: Type], [Predicate])
> checkPatTerms [] = return ([], [], [])
> checkPatTerms (pt : pts) = do
>     (pt', ptBinds, cs) <- checkPatTerm pt
>     (pts', ptsBinds, cs') <- checkPatTerms pts
>     return (pt' : pts', ptBinds ++ ptsBinds, cs ++ cs')

> checkPatTerm :: PatTerm String String ->
>     Contextual () (PatternTerm ::: Type, [TmName ::: Type], [Predicate])
> checkPatTerm (PatVar v) = do
>     nm <- fresh ("_ty" ++ v) (Hole ::: Set)
>     return (PatVar v ::: TyVar nm, [v ::: TyVar nm], [])
> checkPatTerm (PatCon c pts) = do
>     (ty, cs) <- instantiate =<< lookupTmCon c
>     unless (length pts == args ty) $ errConUnderapplied c (args ty) (length pts)
>     (pts', ptsBinds, cs') <- checkPatTerms pts
>     nm <- fresh "_s" (Hole ::: Set)
>     unify ty $ foldr (-->) (TyVar nm) (map tyOf pts')
>     return (PatCon c (map tmOf pts') ::: TyVar nm, ptsBinds, cs ++ cs')