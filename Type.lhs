> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
>              GADTs, TypeOperators, TypeFamilies, RankNTypes,
>              ScopedTypeVariables #-}

> module Type where

> import Data.Foldable hiding (notElem)
> import Data.Traversable
> import Data.List

> import Kit
> import Kind
> import TyNum



> type Type k   = Ty () k
> type Tau    = Type KSet
> type Sigma  = Type KSet
> type Rho    = Type KSet



> data TyKind where
>     TK :: Type k -> Kind k -> TyKind


> data Ty a k where
>     TyVar  :: Var a k                                    -> Ty a k
>     TyCon  :: TyConName -> Kind k                        -> Ty a k
>     TyApp  :: Ty a (l :-> k) -> Ty a l                   -> Ty a k
>     TyNum  :: TyNum (NVar a)                             -> Ty a KNum
>     Bind   :: Binder -> String -> Kind l -> Ty (a, l) k  -> Ty a k
>     Qual   :: Pred (NVar a) -> Ty a k                    -> Ty a k
>     Arr    :: Ty a (KSet :-> KSet :-> KSet)

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
> fogTy = fogTy' []

> fogTy' :: [String] -> Ty a k -> SType
> fogTy' xs (TyVar v)       = STyVar (fogVar xs v)
> fogTy' xs (TyCon c k)     = STyCon c
> fogTy' xs (TyApp f s)     = STyApp (fogTy' xs f) (fogTy' xs s)
> fogTy' xs (TyNum n)       = STyNum (fogTyNum' xs n)
> fogTy' xs (Bind b x k t)  = SBind b y (fogKind k) (fogTy' (y:xs) t)
>   where y = alphaConv x xs
> fogTy' xs (Qual p t)      = SQual (fogPred' xs p) (fogTy' xs t)
> fogTy' xs Arr             = SArr

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



> alphaConvert :: [(String, String)] -> SType -> SType
> alphaConvert xys (STyApp f s) = STyApp (alphaConvert xys f)
>                                        (alphaConvert xys s)
> alphaConvert xys (SBind b a k t) = case lookup a xys of
>     Just y   -> SBind b y k (alphaConvert ((a, y ++ "'") : xys) t)
>     Nothing  -> SBind b a k (alphaConvert xys t)
> alphaConvert xys t = t

> args :: Ty a k -> Int
> args (TyApp (TyApp Arr s) t)  = succ $ args t
> args (Bind Pi x k t)                = succ $ args t
> args (Bind All x k t)               = args t
> args (Qual p t)                     = args t
> args _                              = 0

> splitArgs :: Ty a k -> ([Ty a k], Ty a k)
> splitArgs (TyApp (TyApp Arr s) t) = (s:ss, ty)
>   where (ss, ty) = splitArgs t
> splitArgs t = ([], t)

> getTarget :: Ty a k -> Ty a k
> getTarget (TyApp (TyApp Arr _) ty)  = getTarget ty
> getTarget t                               = t


> targets :: Ty a k -> TyConName -> Bool
> targets (TyCon c k)               t | c == t = True
> targets (TyApp (TyApp Arr _) ty)  t = targets ty t
> targets (TyApp f s)               t = targets f t
> targets (Bind b a k ty)           t = targets ty t
> targets (Qual p ty)               t = targets ty t
> targets _                         _ = False

> numToType :: NormalNum -> Type KNum
> numToType  = TyNum . reifyNum
