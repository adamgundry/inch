> {-# LANGUAGE GADTs, TypeOperators, TypeSynonymInstances, FlexibleInstances,
>              MultiParamTypeClasses, TypeFamilies, StandaloneDeriving #-}

> module TyNum
>     (  NormalNum
>     ,  Monomial
>     ,  Fac(..)
>     ,  SolveResult(..)
>     ,  NormalPredicate
>     ,  normaliseNum
>     ,  normalisePred
>     ,  trivialPred
>     ,  partitionNum
>     ,  isZero
>     ,  reifyNum
>     ,  reifyPred
>     ,  mkVar
>     ,  getConstant
>     ,  getLinearMono
>     ,  solveFor
>     ,  maybeSolveFor
>     ,  substNum
>     ,  numVariables
>     ,  elimNN
>     )
>   where

> import Prelude hiding (all, any, foldr)
> import Control.Applicative
> import Data.Foldable
> import Data.List hiding (all, any, foldr)
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Monoid

> import Kit
> import Kind
> import Type

> type NVar a           = Var a KNum
> type NormalNum        = NormNum ()
> type NormPred a       = Pred (NormNum a)
> type NormalPredicate  = Pred NormalNum


> newtype NormNum a = NN {elimNN :: Map (Mono a) Integer}
>   deriving (Eq, Ord, Show)

> instance a ~ b => FV (NormNum a) b where
>     fvFoldMap f = fvFoldMap f . elimNN

> instance (Ord t, FV t a) => FV (Map t x) a where
>     fvFoldMap f = Map.foldrWithKey (\ t _ m -> fvFoldMap f t <.> m) mempty

> type Mono a    = Map (Fac a KNum) Integer
> type Monomial  = Mono ()

> monoVar :: NVar a -> Mono a
> monoVar v = Map.singleton (VarFac v) 1



> data Fac a k where
>     VarFac  :: Var a k -> Fac a k
>     AppFac  :: Fac a (KNum :-> k) -> NormNum a -> Fac a k
>     UnFac   :: UnOp -> Fac a (KNum :-> KNum)
>     BinFac  :: BinOp -> Fac a (KNum :-> KNum :-> KNum)

> deriving instance Eq (Fac a k)
> deriving instance Show (Fac a k)

> instance Ord (Fac a k) where
>     VarFac a    <= VarFac b    = a <= b
>     VarFac _    <= _           = True
>     _           <= VarFac _    = False
>     AppFac f m  <= AppFac g n  = f <= g && m <= n
>     AppFac _ _  <= _           = True
>     _           <= AppFac _ _  = False
>     UnFac o     <= UnFac p     = o <= p
>     UnFac _     <= _           = True
>     _           <= UnFac _     = False
>     BinFac o    <= BinFac p    = o <= p

> type Factor k = Fac () KNum

> instance a ~ b => FV (Fac a k) b where
>     fvFoldMap f (VarFac a)    = f a
>     fvFoldMap f (AppFac t m)  = fvFoldMap f t <.> fvFoldMap f m
>     fvFoldMap f (UnFac _)     = mempty
>     fvFoldMap f (BinFac _)    = mempty

> singleFac :: Fac a KNum -> NormNum a
> singleFac x = NN (Map.singleton (Map.singleton x 1) 1)



> instance Num (NormNum a) where
>     fromInteger i   | i == 0     = NN Map.empty
>                     | otherwise  = NN $ Map.singleton Map.empty i
>
>     NN xs + NN ys   = NN . dropZeroes $ Map.unionWith (+) xs ys
>
>     negate (NN xs)  = NN $ Map.map negate xs
>
>     m      * n      | Just i <- getConstant m  = i *~ n
>                     | Just j <- getConstant n  = j *~ m
>     NN xs  * NN ys  = NN . dropZeroes $
>            Map.fromList [mk x y | x <- Map.toList xs, y <- Map.toList ys]
>       where
>         mk :: (Mono a, Integer) -> (Mono a, Integer) -> (Mono a, Integer)
>         mk (xs, i) (ys, j) = (dropZeroes $ Map.unionWith (+) xs ys, i*j)


> dropZeroes :: Ord a => Map a Integer -> Map a Integer
> dropZeroes = Map.filter (/= 0)

> (*~) :: Integer -> NormNum a -> NormNum a
> 0 *~ _      = 0
> 1 *~ n      = n
> i *~ NN xs  = NN $ Map.map (i*) xs

> getSingleton :: Map k t -> Maybe (k, t)
> getSingleton xs = case Map.toList xs of
>                     [kt]  -> Just kt
>                     _     -> Nothing

> getConstant :: NormNum a -> Maybe Integer
> getConstant (NN xs)  | Map.null xs                                   = Just 0
>                      | Just (ys, k) <- getSingleton xs, Map.null ys  = Just k
>                      | otherwise                                     = Nothing

> isZero :: NormNum a -> Bool
> isZero = Map.null . elimNN


> mkVar :: Var a KNum -> NormNum a
> mkVar a = NN $ Map.singleton (monoVar a) 1


> numVariables :: NormNum a -> Int
> numVariables = length . nub . vars

> substNum :: Var () KNum -> Type KNum -> NormalNum -> NormalNum
> substNum a t n = normaliseNum (replaceTy a t (reifyNum n))



> data SolveResult t where
>     Absent    :: SolveResult t
>     Solve     :: t -> SolveResult t
>     Simplify  :: t -> SolveResult t
>     Stuck     :: SolveResult t
>   deriving Show

> solveFor :: Var () KNum -> NormalNum -> SolveResult NormalNum
> solveFor a n =
>   let (NN ys, NN zs) = partitionNum [a] n 
>   in case Map.toList ys of
>     []                                                    -> Absent
>     [(m, k)]  | isMono && all (k `divides`) zs            -> Solve t
>               | isMono && any (\ j -> abs k <= abs j) zs  -> Simplify t
>       where
>         isMono         = m == monoVar a
>         t              = NN . dropZeroes $ Map.map q zs
>         q x            = x `quot` (-k)
>         n `divides` m  = m `mod` n == 0
>     _ -> Stuck

> maybeSolveFor :: Var () KNum -> NormalNum -> Maybe NormalNum
> maybeSolveFor a n = case solveFor a n of
>                         Solve t  -> Just t
>                         _        -> Nothing


> partitionNum :: [Var () KNum] -> NormalNum -> (NormalNum, NormalNum)
> partitionNum vs (NN xs) = (NN ls, NN rs)
>   where (ls, rs) = Map.partitionWithKey (const . (vs <<?)) xs

> {-
> getLinear :: NormNum a -> Maybe (Integer, [(NVar a, Integer)])
> getLinear (NN xs) = lin (Map.toList xs)
>   where
>     lin :: [(Mono a, Integer)] -> Maybe (Integer, [(NVar a, Integer)])
>     lin []            = Just (0, [])
>     lin ((ys, k):xs)  = do
>         l <- getLinearMono ys
>         (j, zs) <- lin xs
>         return $ case l of
>             Left ()  -> (j + k, zs)
>             Right a  -> (j, (a,k):zs)
> -}

> getLinearMono :: Mono a -> Maybe (Either () (Fac a KNum))
> getLinearMono xs = case Map.toList xs of
>     []        -> Just (Left ())
>     [(f, 1)]  -> Just (Right f)
>     _         -> Nothing


> reifyNum :: NormNum a -> Ty a KNum
> reifyNum (NN xs) = tySum pos -~ tySum neg
>   where
>     tySum :: [(Mono a, Integer)] -> Ty a KNum
>     tySum = foldr (\ (t, k) u -> (k *** reifyMono t) +++ u) 0

>     pos  = Map.toList posXs
>     neg  = Map.toList (Map.map negate negXs)
>     (posXs, negXs) = Map.partition (> 0) xs
>     
>     (+++) :: Ty a KNum -> Ty a KNum -> Ty a KNum
>     TyInt i  +++ TyInt j  = TyInt (i + j)
>     TyInt 0  +++ t        = t
>     t        +++ TyInt 0  = t
>     t        +++ t'       = t + t'

>     (***) :: Integer -> Ty a KNum -> Ty a KNum
>     i        *** TyInt j  = TyInt (i * j)
>     0        *** _        = 0
>     1        *** t        = t
>     k        *** t        = TyInt k * t

>     (-~) :: Ty a KNum -> Ty a KNum -> Ty a KNum
>     TyInt i  -~ TyInt j   = TyInt (i - j)
>     t        -~ TyInt 0   = t
>     t        -~ t'        = t - t'

>     reifyMono :: Mono a -> Ty a KNum
>     reifyMono = Map.foldrWithKey (\ f k t -> pow (reifyFac f) k **** t) 1

>     (****) :: Ty a KNum -> Ty a KNum -> Ty a KNum
>     TyInt i  **** TyInt j  = TyInt (i * j)
>     TyInt 0  **** _        = TyInt 0
>     _        **** TyInt 0  = TyInt 0
>     TyInt 1  **** t        = t
>     t        **** TyInt 1  = t
>     s        **** t        = s * t

>     reifyFac :: Fac a k -> Ty a k
>     reifyFac (VarFac a)    = TyVar a
>     reifyFac (AppFac f m)  = TyApp (reifyFac f) (reifyNum m)
>     reifyFac (UnFac o)     = UnOp o
>     reifyFac (BinFac o)    = BinOp o

>     pow :: Ty a KNum -> Integer -> Ty a KNum
>     pow _  0  = 1
>     pow t  1  = t
>     pow t  k  = binOp Pow t (fromInteger k)


> reifyPred :: Pred (NormNum a) -> Pred (Ty a KNum)
> reifyPred = fmap reifyNum

> normaliseNum :: Ty a KNum -> NormNum a
> normaliseNum (TyInt i)           = fromInteger i
> normaliseNum (TyVar a)           = mkVar a
> normaliseNum (TyApp (UnOp o) m)  = 
>     let m' = normaliseNum m
>     in case getConstant m' of
>         Just i   -> fromInteger (unOpFun o i)
>         Nothing  -> singleFac (UnFac o `AppFac` m')
> normaliseNum (TyApp (TyApp (BinOp o) m) n) =
>     nbinOp o (normaliseNum m) (normaliseNum n)
> normaliseNum (TyApp (TyVar v@(FVar _ (KNum :-> KNum))) m) =
>     singleFac (VarFac v `AppFac` normaliseNum m)
> normaliseNum (TyApp (TyApp (TyVar v@(FVar _ (KNum :-> KNum :-> KNum))) m) n) =
>     singleFac (VarFac v `AppFac` normaliseNum m `AppFac` normaliseNum n)

> normalisePred :: Pred (Ty a KNum) -> NormPred a
> normalisePred (P c m n) = P c 0 (normaliseNum (n - m))

> trivialPred :: Ord a => NormPred a -> Maybe Bool
> trivialPred (P c m n)     = compFun c 0 <$> (getConstant (n - m))

> nbinOp :: BinOp -> NormNum a -> NormNum a -> NormNum a
> nbinOp o m n = case (o, getConstant m, getConstant n) of
>         (o,      Just i,   Just j)  -> fromInteger (binOpFun o i j)
>         (Plus,   _,        _)       -> m + n
>         (Minus,  _,        _)       -> m - n
>         (Times,  _,        _)       -> m * n
>         (Pow,    _,        Just j)  -> m ^ j
>         (Pow,    Just 1,   _)       -> 1
>         (Pow,    Just 0,   _)       -> 0
>         _                           -> singleFac (BinFac o `AppFac` m `AppFac` n)
