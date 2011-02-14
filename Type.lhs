> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
>              GADTs #-}

> module Type where

> import Data.Foldable
> import Data.Traversable

> import Kit


> type TyName           = (String, Int)
> type TmName           = String
> type TyConName        = String
> type TmConName        = String

> type Type             = Ty TyName
> type TypeNum          = TyNum TyName
> type Predicate        = Pred TyName



> data Kind where
>     Set      :: Kind
>     KindNum  :: Kind
>     KindArr  :: Kind -> Kind -> Kind
>   deriving (Eq, Show)

> k1 ---> k2 = KindArr k1 k2
> infixr 5 --->

> targetsSet :: Kind -> Bool
> targetsSet Set            = True
> targetsSet KindNum        = False
> targetsSet (KindArr _ k)  = targetsSet k 



> data TyNum a where
>     NumConst  :: Integer -> TyNum a
>     NumVar    :: a -> TyNum a
>     (:+:)     :: TyNum a -> TyNum a -> TyNum a
>     (:*:)     :: TyNum a -> TyNum a -> TyNum a
>     Neg       :: TyNum a -> TyNum a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> instance Monad TyNum where
>     return = NumVar
>     NumConst k  >>= f = NumConst k
>     NumVar a    >>= f = f a
>     m :+: n     >>= f = (m >>= f) :+: (n >>= f)
>     m :*: n     >>= f = (m >>= f) :*: (n >>= f)
>     Neg n       >>= f = Neg (n >>= f)

> simplifyNum :: TyNum a -> TyNum a
> simplifyNum (n :+: m) = case (simplifyNum n, simplifyNum m) of
>     (NumConst k,  NumConst l)  -> NumConst (k+l)
>     (NumConst 0,  m')          -> m'
>     (n',          NumConst 0)  -> n'
>     (n',          m')          -> n' :+: m'
> simplifyNum (n :*: m) = case (simplifyNum n, simplifyNum m) of
>     (NumConst k,     NumConst l)     -> NumConst (k*l)
>     (NumConst 0,     m')             -> NumConst 0
>     (NumConst 1,     m')             -> m'
>     (NumConst (-1),  m')             -> Neg m'
>     (n',             NumConst 0)     -> NumConst 0
>     (n',             NumConst 1)     -> n'
>     (n',             NumConst (-1))  -> Neg n'
>     (n',             m')             -> n' :*: m'
> simplifyNum (Neg n) = case simplifyNum n of
>     NumConst k  -> NumConst (-k)
>     n'          -> Neg n'
> simplifyNum t = t

> instance (Eq a, Show a) => Num (TyNum a) where
>     (+)          = (:+:)
>     (*)          = (:*:)
>     negate       = Neg
>     fromInteger  = NumConst
>     abs          = error "no abs"
>     signum       = error "no signum"


> data Pred a where
>     (:<=:) :: TyNum a -> TyNum a -> Pred a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> bindPred :: (a -> TyNum b) -> Pred a -> Pred b
> bindPred g (n :<=: m)  = (n >>= g) :<=: (m >>= g)

> simplifyPred :: Pred a -> Pred a
> simplifyPred (m :<=: n) = simplifyNum m :<=: simplifyNum n


> data Binder where
>     Pi   :: Binder
>     All  :: Binder
>   deriving (Eq, Show)



> data Ty a where
>     TyVar  :: a -> Ty a
>     TyCon  :: TyConName -> Ty a
>     TyApp  :: Ty a -> Ty a -> Ty a
>     Arr    :: Ty a
>     TyNum  :: TyNum a -> Ty a
>     Bind   :: Binder -> String -> Kind -> Ty (S a) -> Ty a
>     Qual   :: Pred a -> Ty a -> Ty a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> instance Monad Ty where
>     return = TyVar
>     TyVar a       >>= g = g a
>     TyCon c       >>= g = TyCon c
>     TyApp f s     >>= g = TyApp (f >>= g) (s >>= g) 
>     Arr           >>= g = Arr
>     TyNum n       >>= g = TyNum (n >>= (toNum . g))
>     Qual p t      >>= g = Qual (bindPred (toNum . g) p) (t >>= g)
>     Bind b x k t  >>= g = Bind b x k (t >>= wk g)

> s --> t = TyApp (TyApp Arr s) t
> infixr 5 -->

> toNum :: Ty a -> TyNum a
> toNum (TyNum n)  = n
> toNum (TyVar a)  = NumVar a
> toNum d          = error $ "toNum: bad!"

> simplifyTy :: Ty a -> Ty a
> simplifyTy (TyNum n)       = TyNum (simplifyNum n)
> simplifyTy (TyApp f s)     = TyApp (simplifyTy f) (simplifyTy s)
> simplifyTy (Bind b x k t)  = Bind b x k (simplifyTy t)
> simplifyTy (Qual p t)      = Qual (simplifyPred p) (simplifyTy t)
> simplifyTy t               = t

> alphaConvert :: [(String, String)] -> Ty a -> Ty a
> alphaConvert xys (TyApp f s) = TyApp (alphaConvert xys f)
>                                      (alphaConvert xys s)
> alphaConvert xys (Bind b a k t) = case lookup a xys of
>     Just y   -> Bind b y k (alphaConvert ((a, y ++ "'") : xys) t)
>     Nothing  -> Bind b a k (alphaConvert xys t)
> alphaConvert xys t = t

> args :: Ty a -> Int
> args (TyApp (TyApp Arr s) t) = succ $ args t
> args (Bind b x k t) = args t
> args (Qual p t) = args t
> args _ = 0

> targets :: Eq a => Ty a -> TyConName -> Bool
> targets (TyCon c)                 t | c == t = True
> targets (TyApp (TyApp Arr _) ty)  t = targets ty t
> targets (TyApp f s)               t = targets f t
> targets (Bind b a k ty)           t = targets ty t
> targets (Qual p ty)               t = targets ty t
> targets _                         _ = False
