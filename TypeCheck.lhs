> {-# LANGUAGE GADTs, TypeOperators #-}

> module TypeCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Data.List
> import Data.Bitraversable

> import BwdFwd
> import Type
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

> goUp :: Type -> Suffix -> Contextual Term Type
> goUp tau _Xi = do
>     st@(St{tValue = t}) <- get
>     case context st of
>       (es :< Layer l) ->
>         case l of         
>             AppLeft () a -> do
>                 put $ st {tValue = a,
>                     context = es <>< _Xi :< Layer (AppRight (t ::: tau) ())}
>                 inferType
>             AppRight (f ::: sigma) () -> do
>                 put $ st {tValue = TmApp f t, context = es <>< _Xi}
>                 tau' <- matchAppTypes sigma tau
>                 goUp tau' F0
>             LamBody (x ::: sigma) () -> do
>                 put $ st {tValue = Lam x (bind x t), context = es}
>                 goUp (sigma --> tau) _Xi
>             AnnotLeft () ty -> do
>                 put $ st {tValue = t :? ty, context = es <>< _Xi}
>                 unify ty tau
>                 goUp ty F0
>             PatternTop _ _ -> do
>                 put $ st {context = es <>< _Xi}
>                 return tau
>       (es :< A e) -> do
>           put $ st {context = es}
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


> specialise :: TypeDef -> Type -> Contextual t Type
> specialise d (TyApp f s)     = TyApp f <$> specialise d s
> specialise d (Bind b x k t)  = do
>     beta <- fresh x (d ::: k)
>     specialise d (unbind beta t)
> specialise d t               = return t

> inferType :: Contextual Term Type
> inferType = getT >>= \ t -> case t of
>     TmVar x -> lookupTmVar x >>= specialise Hole . tyOf >>= flip goUp F0
>     TmCon c -> lookupTmCon c >>= specialise Hole >>= flip goUp F0
>     TmApp f s -> goAppLeft >> inferType
>     Lam x t -> do
>         a <- fresh "a" (Hole ::: Set)
>         goLam (TyVar a)
>         inferType
>     t :? ty -> goAnnotLeft >> inferType


> infer :: Tm String String -> Contextual () (Term ::: Type)
> infer t = inLocation ("in expression " ++ show (prettyHigh t)) $ do
>     t' <- scopeCheckTypes t
>     ty <- withT t' inferType
>     return (t' ::: ty)

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
>     pattys  <- mapM (checkPat (s ::: sty)) pats
>     ty'     <- simplifyTy <$> generalise sty
>     modifyContext (:< Func s ty')
>     return $ FunDecl s (Just ty') (map tmOf pattys)
> checkFunDecl (FunDecl s (Just st) pats@(Pat xs _ _ : _)) = 
>   inLocation ("in declaration of " ++ s) $ do
>     modifyContext (:< Layer FunTop)
>     sty ::: k <- inLocation ("in type " ++ show (prettyHigh st)) $ inferKind B0 st
>     unless (k == Set) $ errKindNotSet k
>     pattys <- mapM (checkPat (s ::: sty)) pats
>     let ty = tyOf (head pattys)
>     ty' <- simplifyTy <$> generalise ty
>     inLocation ("when matching inferred type\n        " ++ show (prettyFst ty')
>         ++ "\n    against given type\n        " ++ show (prettyFst sty)) $
>             specialise Fixed sty >>= unify ty'
>     modifyContext (:< Func s ty')
>     return (FunDecl s (Just sty) (map tmOf pattys))
> checkFunDecl (FunDecl s _ []) =
>   inLocation ("in declaration of " ++ s) $ fail $ "No alternative"

> generalise :: Type -> Contextual () Type
> generalise t = do
>     g <- getContext
>     let (g', t') = help g t
>     putContext g'
>     return t'
>   where
>     help (g :< Layer FunTop) t = (g, t)
>     help (g :< A (((a, n) := Some d ::: k))) t  = help g (subst (a, n) d t)
>     help (g :< A (((a, n) := _ ::: k))) t    = help g (Bind All a k (bind (a, n) t))
>     help (g :< Constraint p) t = help g (Qual p t)

> checkPat :: String ::: Type -> Pat String String ->
>     Contextual () (Pattern ::: Type)
> checkPat (s ::: sty) (Pat xs g t) =
>   inLocation ("in alternative " ++ s ++ " " ++ show (prettyHigh (Pat xs g t))) $ do
>     (ps, btys) <- checkPatTerms xs
>     modifyContext (:< Layer (PatternTop (s ::: sty) btys))
>     t' ::: ty <- infer t
>     let g' = Trivial -- nonsense
>     let oty = foldr (-->) ty (map tyOf ps)
>     unify oty sty
>     return $ Pat (fmap tmOf ps) g' t' ::: oty

> checkPatTerms :: [PatTerm String String] ->
>     Contextual () ([PatternTerm ::: Type], [TmName ::: Type])
> checkPatTerms [] = return ([], [])
> checkPatTerms (pt : pts) = do
>     (pt', ptBinds) <- checkPatTerm pt
>     (pts', ptsBinds) <- checkPatTerms pts
>     return (pt' : pts', ptBinds ++ ptsBinds)

> checkPatTerm :: PatTerm String String ->
>     Contextual () (PatternTerm ::: Type, [TmName ::: Type])
> checkPatTerm (PatVar v) = do
>     nm <- fresh ("_ty" ++ v) (Hole ::: Set)
>     return (PatVar v ::: TyVar nm, [v ::: TyVar nm])
> checkPatTerm (PatCon c pts) = do
>     ty <- lookupTmCon c
>     unless (length pts == args ty) $ errConUnderapplied c (args ty) (length pts)
>     (pts', ptsBinds) <- checkPatTerms pts
>     nm <- fresh "_s" (Hole ::: Set)
>     unify ty $ foldr (-->) (TyVar nm) (map tyOf pts')
>     return (PatCon c (map tmOf pts') ::: TyVar nm, ptsBinds)