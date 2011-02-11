> {-# LANGUAGE GADTs, TypeOperators #-}

> module TypeCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Data.List
> import Data.Bitraversable

> import BwdFwd
> import Syntax
> import Context
> import Unify
> import Orphans
> import Kit
> import Error
> import PrettyPrinter


> lookupTyVar :: Bwd (TyName ::: Kind) -> String -> Contextual t (TyName ::: Kind)
> lookupTyVar (g :< ((b, n) ::: k)) a  | a == b     = return $ (a, n) ::: k
>                                      | otherwise  = lookupTyVar g a
> lookupTyVar B0 a = getContext >>= seek
>   where
>     seek B0 = missingTyVar a
>     seek (g :< A ((t, n) := _ ::: k)) | a == t = return $ (t, n) ::: k
>     seek (g :< _) = seek g

> lookupNumVar :: Bwd (TyName ::: Kind) -> String -> Contextual t TypeNum
> lookupNumVar (g :< ((b, n) ::: k)) a
>     | a == b && k == KindNum  = return $ NumVar (a, n)
>     | a == b                  = fail $ "Type variable " ++ a ++ " is not numeric"
>     | otherwise               = lookupNumVar g a
> lookupNumVar B0 a = getContext >>= seek
>   where
>     seek B0 = missingNumVar a
>     seek (g :< A ((t, n) := _ ::: k))
>         | a == t && k == KindNum = return $ NumVar (t, n)
>         | a == t = fail $ "Type variable " ++ a ++ " is not numeric"
>     seek (g :< _) = seek g

> lookupTmVar :: TmName -> Contextual t (Term ::: Type)
> lookupTmVar x = getContext >>= seek
>   where
>     seek B0 = missingTmVar x
>     seek (g :< Func y ty)                         | x == y = return $ TmVar y ::: ty
>     seek (g :< Layer (LamBody (y ::: ty) ()))     | x == y = return $ TmVar y ::: ty
>     seek (g :< Layer (PatternTop (y ::: ty) bs))  | x == y = return $ TmVar y ::: ty
>                                                   | otherwise = case lookIn bs of
>                                                       Just tt  -> return tt
>                                                       Nothing  -> seek g
>     seek (g :< _) = seek g
>
>     lookIn [] = Nothing
>     lookIn ((y ::: ty) : bs)  | x == y     = Just $ TmVar y ::: ty
>                               | otherwise  = lookIn bs




> inferKind :: Bwd (TyName ::: Kind) -> Ty String -> Contextual t (Type ::: Kind)
> inferKind g (TyVar a)    = (\ (b ::: k) -> TyVar b ::: k) <$> lookupTyVar g a
> inferKind g (TyCon c)    = (TyCon c :::) <$> lookupTyCon c
> inferKind g (TyApp f s)  = do
>     f' ::: k  <- inferKind g f
>     case k of
>         KindArr k1 k2 -> do
>             s' ::: l  <- inferKind g s
>             unless (k1 == l) $ fail $ "Kind domain mismatch: kind " ++ show l
>                                ++ " of " ++ show s ++ " is not " ++ show k1
>             return $ TyApp f' s' ::: k2
>         _ -> fail $ "Kind mismatch: kind " ++ show k ++ " of " ++ show f ++ " is not an arrow"
> inferKind g Arr             = return $ Arr ::: Set ---> Set ---> Set
> inferKind g (TyNum n)       = (\ n -> TyNum n ::: KindNum) <$> checkNumKind g n
> inferKind g (Bind b a k t)  = do
>     n <- freshName
>     ty ::: l <- inferKind (g :< ((a, n) ::: k)) (unbind a t)
>     return $ Bind b a k (bind (a, n) ty) ::: l

> checkNumKind :: Bwd (TyName ::: Kind) -> TyNum String -> Contextual t TypeNum
> checkNumKind g (NumConst k) = return $ NumConst k
> checkNumKind g (NumVar a) = lookupNumVar g a
> checkNumKind g (m :+: n) = (:+:) <$> checkNumKind g m <*> checkNumKind g n
> checkNumKind g (Neg n) = Neg <$> checkNumKind g n




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
>     alpha <- fresh "dom" (Nothing ::: Set)
>     unify sigma (tau --> TyVar alpha)
>     return $ TyVar alpha


> specialise :: Type -> Contextual t Type
> specialise (TyApp f s)     = TyApp f <$> specialise s
> specialise (Bind b x k t)  = do
>     beta <- fresh x (Nothing ::: k)
>     specialise (unbind beta t)
> specialise t               = return t

> inferType :: Contextual Term Type
> inferType = getT >>= \ t -> case t of
>     TmVar x -> lookupTmVar x >>= specialise . tyOf >>= flip goUp F0
>     TmCon c -> lookupTmCon c >>= specialise >>= flip goUp F0
>     TmApp f s -> goAppLeft >> inferType
>     Lam x t -> do
>         a <- fresh "a" (Nothing ::: Set)
>         goLam (TyVar a)
>         inferType
>     t :? ty -> goAnnotLeft >> inferType


> infer :: Tm String String -> Contextual () (Term ::: Type)
> infer t = do
>     t' <- scopeCheckTypes t
>     ty <- withT t' inferType
>     return (t' ::: ty)

> scopeCheckTypes :: Tm String String -> Contextual () Term
> scopeCheckTypes = bitraverse (fmap tmOf . lookupTyVar B0) pure 




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

> targetsSet :: Kind -> Bool
> targetsSet Set            = True
> targetsSet KindNum        = False
> targetsSet (KindArr _ k)  = targetsSet k 

> checkConstructor :: TyConName -> Con String -> Contextual () Constructor
> checkConstructor t (c ::: ty) = inLocation ("in constructor " ++ c) $ do
>     (ty' ::: k) <- inferKind B0 ty
>     unless (k == Set) $ errKindNotSet k
>     unless (ty' `targets` t) $ errConstructorTarget ty'
>     insertTmCon c ty'
>     return (c ::: ty')

> targets :: Eq a => Ty a -> TyConName -> Bool
> targets (TyCon c)                 t | c == t = True
> targets (TyApp (TyApp Arr _) ty)  t = targets ty t
> targets (TyApp f s)               t = targets f t
> targets (Bind b a k ty)           t = targets ty t
> targets _                         _ = False


> checkFunDecl :: FunDecl String String -> Contextual () FunDeclaration
> checkFunDecl (FunDecl s Nothing pats@(Pat xs _ _ : _)) =
>   inLocation ("in declaration of " ++ s) $ do
>     modifyContext (:< Layer FunTop)
>     sty <- TyVar <$> fresh "sty" (Nothing ::: Set)
>     pattys <- unzip <$> mapM (checkPat (s ::: sty)) pats
>     let pts = map (map tyOf) $ fst pattys
>     unless (all ((== length (head pts)) . length) pts) $ fail $ "Arity error in " ++ show s
>     mapM unifyAll (transpose pts)
>     let ttys = map tyOf $ snd pattys
>     unifyAll ttys
>     let ty = foldr (-->) (head ttys) (head pts)
>     unify ty sty
>     ty' <- simplifyTy <$> generalise ty
>     modifyContext (:< Func s ty')
>     return (FunDecl s (Just ty') (map tmOf $ snd pattys))
> checkFunDecl (FunDecl s (Just st) pats@(Pat xs _ _ : _)) = 
>   inLocation ("in declaration of " ++ s) $ do
>     modifyContext (:< Layer FunTop)
>     (sty ::: k) <- inferKind B0 st
>     unless (k == Set) $ errKindNotSet k
>     pattys <- unzip <$> mapM (checkPat (s ::: sty)) pats
>     let pts = map (map tyOf) $ fst pattys
>     unless (all ((== length (head pts)) . length) pts) $ fail $ "Arity error in " ++ show s
>     mapM unifyAll (transpose pts)
>     let ttys = map tyOf $ snd pattys
>     -- unifyAll ttys
>     let ty = foldr (-->) (head ttys) (head pts)
>     ty' <- simplifyTy <$> generalise ty
>         -- "Inferred type " ++ show ty' ++ " for " ++ s ++ " is not " ++ show sty
>     sty' <- specialise sty
>     match ty' sty'
>     modifyContext (:< Func s ty')
>     return (FunDecl s (Just ty') (map tmOf $ snd pattys))

> unifyAll :: [Type] -> Contextual () ()
> unifyAll []         = return ()
> unifyAll [t]        = return ()
> unifyAll (s:t:sts)  = unify s t >> unifyAll (t:sts)

> generalise :: Type -> Contextual () Type
> generalise t = do
>     g <- getContext
>     let (g', t') = help g t
>     putContext g'
>     return t'
>   where
>     help (g :< Layer FunTop) t = (g, t)
>     help (g :< A (((a, n) := Nothing ::: k))) t = help g (Bind All a k (bind (a, n) t))
>     help (g :< A (((a, n) := Just d ::: k))) t = help g (subst (a, n) d t)

> checkPat :: String ::: Type -> Pat String String ->
>     Contextual () ([PatternTerm ::: Type], Pattern ::: Type)
> checkPat (s ::: sty) (Pat xs g t) =
>   inLocation ("in alternative " ++ s ++ " " ++ show (prettyHigh (Pat xs g t))) $ do
>     (ps, btys) <- checkPatTerms xs
>     modifyContext (:< Layer (PatternTop (s ::: sty) btys))
>     t' ::: ty <- infer t
>     let g' = Trivial -- nonsense
>     let oty = foldr (-->) ty (map tyOf ps)
>     unify oty sty
>     return (ps, Pat (fmap tmOf ps) g' t' ::: ty)

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
>     nm <- fresh ("ty" ++ v) (Nothing ::: Set)
>     return (PatVar v ::: TyVar nm, [v ::: TyVar nm])
> checkPatTerm (PatCon c pts) = do
>     ty <- lookupTmCon c
>     unless (length pts == args ty) $ errConUnderapplied c (args ty) (length pts)
>     (pts', ptsBinds) <- checkPatTerms pts
>     nm <- fresh "cod" (Nothing ::: Set)
>     unify ty $ foldr (-->) (TyVar nm) (map tyOf pts')
>     return (PatCon c (map tmOf pts') ::: TyVar nm, ptsBinds)