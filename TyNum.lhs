> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GADTs,
>              TypeSynonymInstances #-}

> module TyNum where

> import Control.Applicative
> import Control.Monad
> import Data.Foldable
> import Data.Traversable

> import Kit
> import Num
> import Kind

> type TypeNum          = TyNum (NVar ())
> type Predicate        = Pred (NVar ())
> type NormalNum        = NormNum (NVar ())
> type NormalPredicate  = NormPred (NVar ())

> type STypeNum         = TyNum String
> type SPredicate       = Pred String
> type SNormalNum       = NormNum String
> type SNormalPred      = NormPred String

> type NVar a = Var a KNum
> type NormNum a = NExp a



> data TyNum t where
>     NumConst  :: Integer               -> TyNum t
>     NumVar    :: t                     -> TyNum t
>     (:+:)     :: TyNum t -> TyNum t  -> TyNum t
>     (:*:)     :: TyNum t -> TyNum t  -> TyNum t
>     Neg       :: TyNum t               -> TyNum t
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

> instance Applicative TyNum where
>     pure = return
>     (<*>) = ap




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


> data Comparator = LE | LS | GE | GR | EL
>   deriving (Eq, Show)

> data Pred a where
>     P  :: Comparator -> TyNum a -> TyNum a -> Pred a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> (%==%) = P EL
> (%<=%) = P LE
> (%<%)  = P LS
> (%>=%) = P GE
> (%>%)  = P GR

> travPred :: Applicative f =>
>     (TyNum a -> f (TyNum b)) -> Pred a -> f (Pred b)
> travPred f (P c m n) = P c <$> f m <*> f n

> mapPred :: (TyNum a -> TyNum b) -> Pred a -> Pred b
> mapPred f = unId . travPred (Id . f)

> simplifyPred :: Pred a -> Pred a
> simplifyPred (P EL m n) = case (simplifyNum m, simplifyNum n) of
>     (m' :+: Neg n', NumConst 0)  -> m' %==% n'
>     (Neg n' :+: m', NumConst 0)  -> m' %==% n'
>     (NumConst 0, m' :+: Neg n')  -> m' %==% n'
>     (NumConst 0, Neg n' :+: m')  -> m' %==% n'
>     (m', n')                     -> m' %==% n'
> simplifyPred p = mapPred simplifyNum p




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


> reifyNum :: Ord a => NormNum a -> TyNum a
> reifyNum = simplifyNum . foldNExp (\ k n m -> NumConst k :*: NumVar n :+: m) NumConst

> normalNum :: Ord a => TyNum a -> NormNum a
> normalNum n = either error id $ normaliseNum n



> data NormPred a where
>     IsPos   :: NormNum a -> NormPred a
>     IsZero  :: NormNum a -> NormPred a
>   deriving (Eq, Show)

> mapNormPred :: (NormNum a -> NormNum b) -> NormPred a -> NormPred b
> mapNormPred f (IsPos n)   = IsPos (f n)
> mapNormPred f (IsZero n)  = IsZero (f n)

> bindNormPred :: (Eq a, Eq b) => (a -> NormNum b) -> NormPred a -> NormPred b
> bindNormPred g (IsPos n)   = IsPos   (bindNExp g n)
> bindNormPred g (IsZero n)  = IsZero  (bindNExp g n)

> substNormPred :: Eq a => a -> NormNum a -> NormPred a -> NormPred a
> substNormPred a n (IsPos m)   = IsPos   $ substNum a n m
> substNormPred a n (IsZero m)  = IsZero  $ substNum a n m

> reifyPred :: Ord a => NormPred a -> Pred a
> reifyPred (IsPos n) = NumConst 0 %<=% reifyNum n
> reifyPred (IsZero n) = reifyNum n %==% NumConst 0

> normalisePred :: (Ord a, Applicative m, Monad m) => Pred a -> m (NormPred a)
> normalisePred (P LE m n)  = IsPos <$> normaliseNum (n :+: Neg m)
> normalisePred (P LS m n)  = IsPos <$> normaliseNum (n :+: Neg (m :+: NumConst 1))
> normalisePred (P GE m n)  = IsPos <$> normaliseNum (m :+: Neg n)
> normalisePred (P GR m n)  = IsPos <$> normaliseNum (m :+: Neg (n :+: NumConst 1))
> normalisePred (P EL m n)  = IsZero <$> normaliseNum (n :+: Neg m)

> normalPred p = either error id $ normalisePred p



> subsTyNum :: Applicative f =>
>     (a -> f (TyNum b)) ->
>     TyNum a -> f (TyNum b)
> subsTyNum fn (NumVar a)    = fn a
> subsTyNum fn (NumConst k)  = pure $ NumConst k
> subsTyNum fn (n :+: m)     = (:+:) <$> subsTyNum fn n <*> subsTyNum fn m
> subsTyNum fn (n :*: m)     = (:*:) <$> subsTyNum fn n <*> subsTyNum fn m
> subsTyNum fn (Neg n)       = Neg <$> subsTyNum fn n

> subsPred :: Applicative f =>
>     (a -> f (TyNum b)) ->
>     Pred a -> f (Pred b)
> subsPred fn (P c m n) = P c <$> subsTyNum fn m <*> subsTyNum fn n

> bindPred :: (a -> TyNum b) -> Pred a -> Pred b
> bindPred f = unId . subsPred (Id . f)



> fogTyNum :: TypeNum -> STypeNum
> fogTyNum = fogTyNum' []

> fogTyNum' :: [String] -> TyNum (NVar a) -> STypeNum
> fogTyNum' xs = fmap (fogVar xs)

> fogPred :: Predicate -> SPredicate
> fogPred = fogPred' []

> fogPred' :: [String] -> Pred (NVar a) -> SPredicate
> fogPred' xs = mapPred (fogTyNum' xs)

> fogNormNum :: NormalNum -> SNormalNum
> fogNormNum = fogNormNum' []

> fogNormNum' :: [String] -> NormNum (NVar a) -> SNormalNum
> fogNormNum' xs = fmap (fogVar xs)

> fogNormPred :: NormalPredicate -> SNormalPred
> fogNormPred = fogNormPred' []

> fogNormPred' :: [String] -> NormPred (NVar a) -> SNormalPred
> fogNormPred' xs = mapNormPred (fogNormNum' xs)
