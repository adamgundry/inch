> {-# LANGUAGE GADTs, TypeOperators #-}

> module TypeCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Data.List

> import BwdFwd
> import Syntax
> import Context
> import Unify


> lookupTyVar :: Bwd (TyName ::: Kind) -> String -> Contextual t (Type ::: Kind)
> lookupTyVar (g :< ((b, n) ::: k)) a  | a == b     = return $ TyVar (a, n) ::: k
>                                      | otherwise  = lookupTyVar g a
> lookupTyVar B0 a = getContext >>= seek
>   where
>     seek B0 = fail $ "Missing type variable " ++ a
>     seek (g :< A ((t, n) := _ ::: k)) | a == t = return $ TyVar (t, n) ::: k
>     seek (g :< _) = seek g

> lookupTyCon :: String -> Contextual t (Type ::: Kind)
> lookupTyCon a = getContext >>= seek
>   where
>     seek B0 = fail $ "Missing type constructor " ++ a
>     seek (g :< Data (t, n) k _) | a == t = return $ TyCon (t, n) ::: k
>     seek (g :< _) = seek g

> inferKind :: Bwd (TyName ::: Kind) -> Ty String -> Contextual t (Type ::: Kind)
> inferKind g (TyVar a)    = lookupTyVar g a
> inferKind g (TyCon c)    = lookupTyCon c
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
> inferKind g (Bind b a k t)  = do
>     n <- freshName
>     ty ::: l <- inferKind (g :< ((a, n) ::: k)) (unbind a t)
>     return $ Bind b a k (bind (a, n) ty) ::: l





> goLam :: Type -> Contextual Term ()
> goLam tau = modify g
>   where g (n, Lam x t, es) = (n, unbind x t, es :< Layer (LamBody (x ::: tau) ()))


|goAppLeft| descends left into an application.

> goAppLeft :: Contextual Term ()
> goAppLeft = modify g
>   where g (n, TmApp f s, es) = (n, f, es :< Layer (AppLeft () s))




|goUp tau acc| is called when the term at the current location has
been given type |tau|, and it proceeds up and then right to find
the next type inference problem.

The accumulator |acc| collects variable definitions that |tau| may depend
on, and hence must be reinserted into the context once the new location
is found.

> goUp :: Type -> Suffix -> Contextual Term Type
> goUp tau _Xi = do
>     (n, t, _Gamma) <- get
>     case _Gamma of
>       (es :< Layer l) ->
>         case l of         
>             AppLeft () a -> do
>                 put (n, a, es <>< _Xi :< Layer (AppRight (t ::: tau) ()))
>                 inferType
>             AppRight (f ::: sigma) () -> do
>                 put (n, TmApp f t, es <>< _Xi)
>                 tau' <- matchAppTypes sigma tau
>                 goUp tau' F0
>             LamBody (x ::: sigma) () -> do
>                 put (n, Lam x (bind x t), es) 
>                 goUp (sigma --> tau) _Xi
>             PatternTop _ _ -> do
>                 put (n, t, es <>< _Xi) 
>                 return tau
>       (es :< A e) ->
>           put (n, t, es) >>
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




> lookupTm :: String -> Contextual t Type
> lookupTm x = getContext >>= seek
>   where
>     seek B0 = fail $ "Missing term variable " ++ x
>     seek (g :< Func y ty)                         | x == y = return ty
>     seek (g :< Layer (LamBody (y ::: ty) ()))     | x == y = return ty
>     seek (g :< Layer (PatternTop (y ::: ty) bs))  | x == y = return ty
>                                                   | Just ty <- lookIn bs = return ty
>     seek (g :< _) = seek g

>     lookIn [] = Nothing
>     lookIn ((y ::: ty) : bs)  | x == y = Just ty
>                               | otherwise = lookIn bs

> lookupCon :: String -> Contextual t Type
> lookupCon x = getContext >>= seek
>   where
>     seek B0 = fail $ "Missing data constructor " ++ x
>     seek (g :< Data d k cs) = seekIn cs `mplus` seek g
>     seek (g :< _) = seek g
>
>     seekIn [] = mzero
>     seekIn (Con c ty : cs) | x == c     = return ty
>                            | otherwise  = seekIn cs

> specialise :: Type -> Contextual t Type
> specialise (TyVar a)       = return $ TyVar a
> specialise (TyCon c)       = return $ TyCon c
> specialise (TyApp f s)     = TyApp <$> specialise f <*> specialise s
> specialise Arr             = return $ Arr
> specialise (Bind b x k t)  = do
>     beta <- fresh x (Nothing ::: k)
>     specialise (unbind beta t)

> inferType :: Contextual Term Type
> inferType = getT >>= \ t -> case t of
>     TmVar x -> lookupTm x >>= specialise >>= flip goUp F0
>     TmCon c -> lookupCon c >>= specialise >>= flip goUp F0
>     TmApp f s -> do
>         goAppLeft
>         inferType
>     Lam x t -> do
>         a <- fresh "a" (Nothing ::: Set)
>         goLam (TyVar a)
>         inferType


> infer :: Term -> Contextual () Type
> infer t = withT t inferType





> typeCheck p = runStateT (checkProg p) (0, (), B0)

> checkProg :: Prog String String -> Contextual () Program
> checkProg = mapM checkDecl 

> checkDecl :: Decl String String -> Contextual () Declaration
> checkDecl (DD d) = DD <$> checkDataDecl d
> checkDecl (FD f) = FD <$> checkFunDecl f
>     

> checkDataDecl :: DataDecl String String -> Contextual () DataDeclaration
> checkDataDecl (DataDecl t k cs) = do
>     unless (targetsSet k) $ fail $ "Kind of " ++ show t ++ " doesn't target *"
>     n <- freshName 
>     modifyContext (:< Data (t, n) k [])
>     cs' <- mapM (checkConstructor (t, n)) cs
>     modifyContext (replaceData n cs')
>     return (DataDecl (t, n) k cs')
>   where
>     replaceData n cs' (_Gamma :< Data am l [])
>         | am == (t, n) && k == l = _Gamma :< Data am l cs'
>     replaceData n cs' _Gamma = error "wrong thing on end of context"

> targetsSet :: Kind -> Bool
> targetsSet Set            = True
> targetsSet KindNat        = False
> targetsSet (KindArr _ k)  = targetsSet k 

> checkConstructor :: TyName -> Con String String -> Contextual () Constructor
> checkConstructor t (Con c ty) = do
>     (ty' ::: k) <- inferKind B0 ty
>     unless (k == Set) $ fail $ "Kind of constructor " ++ c ++ " is not *"
>     unless (ty' `targets` t) $ fail $ "Type of constructor " ++ c
>                                         ++ " doesn't target " ++ show t
>     return (Con c ty')

> targets :: Eq a => Ty a -> a -> Bool
> targets (TyCon c)                 t | c == t = True
> targets (TyApp (TyApp Arr _) ty)  t = targets ty t
> targets (TyApp f s)               t = targets f t
> targets (Bind b a k ty)           t = targets ty (S t)
> targets _                         _ = False


> checkFunDecl :: FunDecl String String -> Contextual () FunDeclaration
> checkFunDecl (FunDecl s mty pats@(Pat xs _ _ : _)) = do
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
>     ty' <- generalise ty
>     modifyContext (:< Func s ty')
>     return (FunDecl s (Just ty') (map tmOf $ snd pattys))

> unifyAll :: [Type] -> Contextual () ()
> unifyAll [] = return ()
> unifyAll [t] = return ()
> unifyAll (s:t:sts) = unify s t >> unifyAll (t:sts)

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

> checkPat :: String ::: Type -> Pat String ->
>     Contextual () ([PatternTerm ::: Type], Pattern ::: Type)
> checkPat (s ::: sty) (Pat xs g t) = do
>     (ps, btys) <- checkPatTerms xs
>     modifyContext (:< Layer (PatternTop (s ::: sty) btys))
>     ty <- infer t
>     return (ps, Pat xs g t ::: ty)

> checkPatTerms :: [PatTerm String] ->
>     Contextual () ([PatternTerm ::: Type], [TmName ::: Type])
> checkPatTerms [] = return ([], [])
> checkPatTerms (pt : pts) = do
>     (pt', ptBinds) <- checkPatTerm pt
>     (pts', ptsBinds) <- checkPatTerms pts
>     return (pt' : pts', ptBinds ++ ptsBinds)

> checkPatTerm :: PatTerm String ->
>     Contextual () (PatternTerm ::: Type, [TmName ::: Type])
> checkPatTerm (PatVar v) = do
>     nm <- fresh ("ty" ++ v) (Nothing ::: Set)
>     return (PatVar v ::: TyVar nm, [v ::: TyVar nm])
> checkPatTerm (PatCon c pts) = do
>     ty <- lookupCon c
>     (pts', ptsBinds) <- checkPatTerms pts
>     nm <- fresh "cod" (Nothing ::: Set)
>     unify ty $ foldr (-->) (TyVar nm) (map tyOf pts')
>     return (PatCon c (map tmOf pts') ::: TyVar nm, ptsBinds)

> instance Monad m => Applicative (StateT s m) where
>     pure = return
>     (<*>) = ap