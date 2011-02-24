> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GADTs #-}

> module TyNum where

> import Control.Applicative
> import Data.Foldable
> import Data.Traversable

> import Kit
> import Num

> type TypeNum          = TyNum TyName
> type Predicate        = Pred TyName

> type STypeNum         = TyNum String
> type SPredicate       = Pred String



> data TyNum a where
>     NumConst  :: Integer -> TyNum a
>     NumVar    :: a -> TyNum a
>     (:+:)     :: TyNum a -> TyNum a -> TyNum a
>     (:*:)     :: TyNum a -> TyNum a -> TyNum a
>     Neg       :: TyNum a -> TyNum a
>   deriving (Show, Functor, Foldable, Traversable)

> instance Ord a => Eq (TyNum a) where
>     n == m = case (normaliseNum n, normaliseNum m) of
>         (Just n',  Just m')  -> n' == m'
>         (Nothing,  Nothing)  -> n == m
>         _                    -> False

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
>     (n' :+: NumConst k, NumConst l) | k == -l    -> n'
>                                     | otherwise  -> n' :+: NumConst (k+l)
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

> instance (Ord a, Show a) => Num (TyNum a) where
>     (+)          = (:+:)
>     (*)          = (:*:)
>     negate       = Neg
>     fromInteger  = NumConst
>     abs          = error "no abs"
>     signum       = error "no signum"


> data Pred a where
>     (:<=:) :: TyNum a -> TyNum a -> Pred a
>     (:==:) :: TyNum a -> TyNum a -> Pred a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> bindPred :: (a -> TyNum b) -> Pred a -> Pred b
> bindPred g (n :<=: m)  = (n >>= g) :<=: (m >>= g)
> bindPred g (n :==: m)  = (n >>= g) :==: (m >>= g)

> simplifyPred :: Pred a -> Pred a
> simplifyPred (m :<=: n) = simplifyNum m :<=: simplifyNum n
> simplifyPred (m :==: n) = simplifyNum m :==: simplifyNum n

> type NormNum a = NExp a
> type NormalNum = NormNum TyName

> normaliseNum :: (Ord a, Applicative m, Monad m) => TyNum a -> m (NormNum a)
> normaliseNum (NumConst k)  = return $ mkConstant k
> normaliseNum (NumVar a)    = return $ mkVar a
> normaliseNum (m :+: n)     = (+~) <$> normaliseNum m <*> normaliseNum n
> normaliseNum (m :*: n)     = do
>     m'  <- normaliseNum m
>     n'  <- normaliseNum n
>     case (getConstant m', getConstant n') of
>         (Just i,   Just j)   -> return $ mkConstant (i * j)
>         (Just i,   Nothing)  -> return $ i *~ n'
>         (Nothing,  Just j)   -> return $ j *~ m'
>         (Nothing,  Nothing)  -> fail "Non-linear numeric expression"
> normaliseNum (Neg n)       = negateNExp <$> normaliseNum n


> reifyNum :: NormalNum -> TypeNum
> reifyNum = simplifyNum . foldNExp (\ k n m -> NumConst k * NumVar n + m) NumConst

> normalNum :: Ord a => TyNum a -> NormNum a
> normalNum n = either error id $ normaliseNum n

