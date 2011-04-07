> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
>              GADTs, TypeOperators, TypeFamilies, RankNTypes,
>              ScopedTypeVariables, FlexibleInstances #-}

> module Type where

> import Data.Foldable hiding (notElem)
> import Data.List

> import Kit
> import Kind
> import TyNum



> type Type k  = Ty () k
> type Tau     = Type KSet
> type Sigma   = Type KSet
> type Rho     = Type KSet



> data TyKind where
>     TK :: Type k -> Kind k -> TyKind

> data Binder where
>     Pi   :: Binder
>     All  :: Binder
>   deriving (Eq, Show)


> data Ty a k where
>     TyVar  :: Var a k                                    -> Ty a k
>     TyCon  :: TyConName -> Kind k                        -> Ty a k
>     TyApp  :: Ty a (l :-> k) -> Ty a l                   -> Ty a k
>     TyNum  :: TyNum (NVar a)                             -> Ty a KNum
>     Bind   :: Binder -> String -> Kind l -> Ty (a, l) k  -> Ty a k
>     Qual   :: Pred (NVar a) -> Ty a k                    -> Ty a k
>     Arr    :: Ty a (KSet :-> KSet :-> KSet)

> instance FV (Ty () k) where
>     a <? t = elemTy a t

> data SType where
>     STyVar  :: String                                     -> SType
>     STyCon  :: TyConName                                  -> SType
>     STyApp  :: SType -> SType                             -> SType
>     STyNum  :: TyNum String                               -> SType
>     SBind   :: Binder -> String -> SKind -> SType         -> SType
>     SQual   :: Pred String -> SType                       -> SType
>     SArr    ::                                               SType
>   deriving (Eq, Show)

> fogTy :: Type k -> SType
> fogTy = fogTy' fogVar []

> fogSysTy :: Type k -> SType
> fogSysTy = fogTy' fogSysVar []

> fogTy' :: (forall l. Var a l -> String) -> [String] -> Ty a k -> SType
> fogTy' g xs (TyVar v)       = STyVar (g v)
> fogTy' g xs (TyCon c k)     = STyCon c
> fogTy' g xs (TyApp f s)     = STyApp (fogTy' g xs f) (fogTy' g xs s)
> fogTy' g xs (TyNum n)       = STyNum (fogTyNum' g n)
> fogTy' g xs (Qual p t)      = SQual (fogPred' g p) (fogTy' g xs t)
> fogTy' g xs Arr             = SArr
> fogTy' g xs (Bind b x k t)  =
>     SBind b y (fogKind k) (fogTy' (wkn g) (y:xs) t)
>   where
>     y = alphaConv x xs

>     wkn :: (forall l. Var a l -> String) -> Var (a, k) l -> String
>     wkn g (BVar Top)      = y
>     wkn g (BVar (Pop x))  = g (BVar x)
>     wkn g (FVar a k)      = g (FVar a k)

> alphaConv :: String -> [String] -> String
> alphaConv x xs | x `notElem` xs = x
>                | otherwise = alphaConv (x ++ "'") xs

> getTyKind :: Type k -> Kind k
> getTyKind (TyVar v)       = varKind v
> getTyKind (TyCon c k)     = k
> getTyKind (TyApp f s)     = case getTyKind f of _ :-> k -> k
> getTyKind (TyNum n)       = KNum
> getTyKind (Qual _ t)      = getTyKind t
> getTyKind Arr             = KSet :-> KSet :-> KSet

> s --> t = TyApp (TyApp Arr s) t
> infixr 5 -->

> s ---> t = STyApp (STyApp SArr s) t
> infixr 5 --->


> (/->) :: Foldable f => f (Ty a KSet) -> Ty a KSet -> Ty a KSet
> ts /-> t = Data.Foldable.foldr (-->) t ts

> (/=>) :: Foldable f => f (Pred (NVar a)) -> Ty a k -> Ty a k
> ps /=> t = Data.Foldable.foldr Qual t ps

> toNum :: Ty a KNum -> TyNum (NVar a)
> toNum (TyNum n)  = n
> toNum (TyVar v)  = NumVar v


> withBVar :: (BVar a k -> BVar b k) -> Var a k -> Var b k
> withBVar f (FVar a k)  = FVar a k
> withBVar f (BVar x)    = BVar (f x)

> wkVar :: Var a k -> Var (a, l) k
> wkVar = withBVar Pop

> swapTop :: Ty ((a, k), l) x -> Ty ((a, l), k) x
> swapTop = renameTy (withBVar swapVar)
>   where
>     swapVar :: BVar ((a, k), l) x -> BVar ((a, l), k) x
>     swapVar Top            = Pop Top
>     swapVar (Pop Top)      = Top
>     swapVar (Pop (Pop x))  = Pop (Pop x)

> wkRenaming :: (Var a k -> Var b k) -> Var (a, l) k -> Var (b, l) k
> wkRenaming g (FVar a k)      = wkVar . g $ FVar a k
> wkRenaming g (BVar Top)      = BVar Top
> wkRenaming g (BVar (Pop x))  = wkVar . g $ BVar x

> renameTy :: (forall k. Var a k -> Var b k) -> Ty a l -> Ty b l
> renameTy g (TyVar v)       = TyVar (g v)
> renameTy g (TyCon c k)     = TyCon c k
> renameTy g (TyApp f s)     = TyApp (renameTy g f) (renameTy g s)
> renameTy g (TyNum n)       = TyNum (fmap g n)
> renameTy g (Bind b x k t)  = Bind b x k (renameTy (wkRenaming g) t)
> renameTy g (Qual p t)      = Qual (fmap g p) (renameTy g t)
> renameTy g Arr             = Arr

> bindTy :: Var a k -> Ty a l -> Ty (a, k) l
> bindTy v = renameTy (\ w -> hetEq v w (BVar Top) (wkVar w))

> unbindTy :: Var a k -> Ty (a, k) l -> Ty a l
> unbindTy v = renameTy (\ w -> case w of
>                                 BVar Top      -> v
>                                 BVar (Pop x)  -> BVar x
>                                 FVar a k      -> FVar a k)


> wkTy :: Ty a k -> Ty (a, l) k
> wkTy = renameTy wkVar

> wkSubst :: (Var a k -> Ty b k) -> Var (a, l) k -> Ty (b, l) k
> wkSubst g (FVar a k)      = wkTy (g (FVar a k))
> wkSubst g (BVar Top)      = TyVar (BVar Top)
> wkSubst g (BVar (Pop x))  = wkTy (g (BVar x))

> substTy :: (forall k . Var a k -> Ty b k) -> Ty a l -> Ty b l
> substTy g (TyVar v)       = g v
> substTy g (TyCon c k)     = TyCon c k
> substTy g (TyApp f s)     = TyApp (substTy g f) (substTy g s)
> substTy g (TyNum n)       = TyNum (toNum . g =<< n)
> substTy g (Bind b x k t)  = Bind b x k (substTy (wkSubst g) t)
> substTy g (Qual p t)      = Qual (bindPred (toNum . g) p) (substTy g t)
> substTy g Arr             = Arr


> replaceTy :: forall a k l. Var a k -> Ty a k -> Ty a l -> Ty a l
> replaceTy a u = substTy f
>   where
>     f :: Var a k' -> Ty a k'
>     f b = hetEq a b u (TyVar b)



> simplifyTy :: Ord a => Ty a k -> Ty a k
> simplifyTy = simplifyTy' []
>   where
>     simplifyTy' :: Ord a => [Pred (NVar a)] -> Ty a k -> Ty a k
>     simplifyTy' ps (TyNum n)       = nub ps /=> TyNum (simplifyNum n)
>     simplifyTy' ps (TyApp f s)     = nub ps /=> TyApp (simplifyTy f) (simplifyTy s)
>     -- simplifyTy' ps (Bind b x k t)  = Bind b x k (simplifyTy' (map (fmap S) ps) t)
>     simplifyTy' ps (Qual p t)      = simplifyTy' (simplifyPred p:ps) t
>     simplifyTy' ps t               = nub ps /=> t



> args :: Ty a k -> Int
> args (TyApp (TyApp Arr _) t)  = succ $ args t
> args (Bind Pi  _ _ t)                = succ $ args t
> args (Bind All _ _ t)               = args t
> args (Qual _ t)                     = args t
> args _                              = 0

> splitArgs :: Ty a k -> ([Ty a k], Ty a k)
> splitArgs (TyApp (TyApp Arr s) t) = (s:ss, ty)
>   where (ss, ty) = splitArgs t
> splitArgs t = ([], t)

> getTarget :: Ty a k -> Ty a k
> getTarget (TyApp (TyApp Arr _) ty)  = getTarget ty
> getTarget t                               = t


> targets :: Ty a k -> TyConName -> Bool
> targets (TyCon c _)               t | c == t = True
> targets (TyApp (TyApp Arr _) ty)  t = targets ty t
> targets (TyApp f _)               t = targets f t
> targets (Bind _ _ _ ty)           t = targets ty t
> targets (Qual _ ty)               t = targets ty t
> targets _                         _ = False

> numToType :: NormalNum -> Type KNum
> numToType  = TyNum . reifyNum


> elemTy :: Var a k -> Ty a l -> Bool
> elemTy a (TyVar b)       = a =?= b
> elemTy a (TyCon _ _)     = False
> elemTy a (TyApp f s)     = elemTy a f || elemTy a s
> elemTy a (TyNum n)       = elemTyNum a n
> elemTy a (Bind b x k t)  = elemTy (wkVar a) t
> elemTy a (Qual p t)      = elemPred a p || elemTy a t 
> elemTy a Arr             = False
