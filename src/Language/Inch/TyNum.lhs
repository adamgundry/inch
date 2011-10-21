> {-# LANGUAGE GADTs, TypeOperators, TypeSynonymInstances, FlexibleInstances,
>              MultiParamTypeClasses, TypeFamilies, StandaloneDeriving,
>              PatternGuards #-}

> module Language.Inch.TyNum
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
>     ,  solveForAny
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

> import Language.Inch.Kit
> import Language.Inch.Kind
> import Language.Inch.Type

> type NVar a           = Var a KNum
> type NormalNum        = NormNum ()
> type NormPred a       = Pred (NormNum a)
> type NormalPredicate  = Pred NormalNum


> newtype NormNum a = NN {elimNN :: Map (Mono a) Integer}
>   deriving (Eq, Ord, Show)

> instance a ~ b => FV (NormNum a) b where
>     fvFoldMap f = fvFoldMap f . elimNN

> type Mono a    = Map (Fac a KNum) Integer
> type Monomial  = Mono ()

> monoVar :: NVar a -> Mono a
> monoVar v = Map.singleton (VarFac v) 1

> singleMono :: Mono a -> NormNum a
> singleMono x = NN (Map.singleton x 1)


> data Fac a k where
>     VarFac  :: Var a k -> Fac a k
>     AppFac  :: Fac a (KNum :-> k) -> NormNum a -> Fac a k
>     AptFac  :: Fac a (k' :-> k) -> Ty a k' -> Fac a k
>     UnFac   :: UnOp -> Fac a (KNum :-> KNum)
>     BinFac  :: BinOp -> Fac a (KNum :-> KNum :-> KNum)

> deriving instance Show (Fac a k)

> instance HetEq (Fac a) where
>     hetEq (VarFac a)    (VarFac b)    yes no = hetEq a b yes no
>     hetEq (AppFac f m)  (AppFac g n)  yes no | m == n = hetEq f g yes no
>     hetEq (AptFac f s)  (AptFac g t)  yes no = hetEq f g (hetEq s t yes no) no
>     hetEq (UnFac o)     (UnFac o')    yes no | o == o' = yes
>     hetEq (BinFac o)    (BinFac o')   yes no | o == o' = yes
>     hetEq _             _             _   no = no

> instance Eq (Fac a k) where
>     (==) = (=?=)

> instance HetOrd (Fac a) where
>     VarFac a    <?= VarFac b    = a <?= b
>     VarFac _    <?= _           = True
>     _           <?= VarFac _    = False
>     AppFac f m  <?= AppFac g n  = f <?= g && m <= n
>     AppFac _ _  <?= _           = True
>     _           <?= AppFac _ _  = False
>     AptFac f s  <?= AptFac g t  = f <?= g && s <?= t
>     AptFac _ _  <?= _           = True
>     _           <?= AptFac _ _  = False
>     UnFac o     <?= UnFac p     = o <= p
>     UnFac _     <?= _           = True
>     _           <?= UnFac _     = False
>     BinFac o    <?= BinFac p    = o <= p

> instance Ord (Fac a k) where
>     (<=) = (<?=)

> type Factor k = Fac () k

> instance a ~ b => FV (Fac a k) b where
>     fvFoldMap f (VarFac a)    = f a
>     fvFoldMap f (AppFac t m)  = fvFoldMap f t <.> fvFoldMap f m
>     fvFoldMap f (AptFac t s)  = fvFoldMap f t <.> fvFoldMap f s
>     fvFoldMap f (UnFac _)     = mempty
>     fvFoldMap f (BinFac _)    = mempty

> singleFac :: Fac a KNum -> NormNum a
> singleFac x = singleMono (Map.singleton x 1)



> instance Num (NormNum a) where
>     fromInteger i   | i == 0     = NN Map.empty
>                     | otherwise  = NN $ Map.singleton Map.empty i
>     (+)     = nbinOp Plus
>     (-)     = nbinOp Minus
>     (*)     = nbinOp Times
>     abs     = nunOp Abs
>     signum  = nunOp Signum


> dropZeroes :: Ord a => Map a Integer -> Map a Integer
> dropZeroes = Map.filter (/= 0)

> unionMaps :: Ord a => Map a Integer -> Map a Integer -> Map a Integer
> unionMaps a b = dropZeroes $ Map.unionWith (+) a b

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

> solveForAny :: NormalNum -> Maybe (Var () KNum, NormalNum)
> solveForAny n = msum [(\ x -> (a, x)) <$> maybeSolveFor a n | a <- numvars n]

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
>     reifyFac (AptFac f t)  = TyApp (reifyFac f) t
>     reifyFac (UnFac o)     = UnOp o
>     reifyFac (BinFac o)    = BinOp o

>     pow :: Ty a KNum -> Integer -> Ty a KNum
>     pow _  0  = 1
>     pow t  1  = t
>     pow t  k  = binOp Pow t (fromInteger k)


> reifyPred :: Pred (NormNum a) -> Pred (Ty a KNum)
> reifyPred = fmap reifyNum

> normaliseNum :: Type KNum -> NormalNum
> normaliseNum (TyInt i)  = fromInteger i
> normaliseNum t          = facToNum (factorise t)
>   where
>     factorise :: Type k -> Factor k
>     factorise (TyVar a)    = VarFac a
>     factorise (UnOp o)     = UnFac o
>     factorise (BinOp o)    = BinFac o
>     factorise (TyApp f s)  = case getTyKind s of
>                                  KNum  -> factorise f `AppFac` normaliseNum s
>                                  _     -> factorise f `AptFac` s
>     factorise t = error $ "normaliseNum: can't factorise " ++ show t
>
>     facToNum :: Factor KNum -> NormalNum
>     facToNum (UnFac o `AppFac` m)              = nunOp o m
>     facToNum (BinFac o `AppFac` m `AppFac` n)  = nbinOp o m n
>     facToNum f                                 = singleFac f

> normalisePred :: Predicate -> NormalPredicate
> normalisePred (P c m n) = P c 0 (normaliseNum (n - m))
> normalisePred (p :=> q) = normalisePred p :=> normalisePred q

> trivialPred :: Ord a => NormPred a -> Maybe Bool
> trivialPred (P c m n)     = compFun c 0 <$> (getConstant (n - m))
> trivialPred (p :=> q)     = case trivialPred p of
>                                 Just False  -> Just True
>                                 _           -> trivialPred q

> nunOp :: UnOp -> NormNum a -> NormNum a
> nunOp o m = case getConstant m of
>                 Just i   -> fromInteger (unOpFun o i)
>                 Nothing  -> singleFac (UnFac o `AppFac` m)

> nbinOp :: BinOp -> NormNum a -> NormNum a -> NormNum a
> nbinOp o m n = case (o, getConstant m, getConstant n) of
>         (Pow,    Just i,   Just j)  | j >= 0     -> fromInteger (i ^ j)
>         (Pow,    _,        Just j)  | j >= 0     -> m ^ j
>                                     | otherwise  -> singleFac (BinFac Pow `AppFac` m `AppFac` n)
>         (Pow,    Just 1,   _)       -> 1
>         (Pow,    _,        _)       -> foldr foo 1 (Map.toList $ elimNN n)
>           where
>             foo (x, k) t | Map.null x  = t * (m ^ k)
>                          | otherwise   = t * (singleFac (BinFac Pow `AppFac` m `AppFac` singleMono x) ^ k)

>         (o,      Just i,   Just j)  -> fromInteger (binOpFun o i j)
>         (Plus,   _,        _)       -> NN $ unionMaps (elimNN m) (elimNN n)
>         (Minus,  _,        _)       -> NN $ unionMaps (elimNN m) (Map.map negate $ elimNN n)
>         (Times,  Just i,   _)       -> i *~ n
>         (Times,  _,        Just j)  -> j *~ m
>         (Times,  _,        _)       -> NN . dropZeroes . Map.fromList $ 
>             [(unionMaps xs ys, i*j)
>                 | (xs, i) <- Map.toList (elimNN m), (ys, j) <- Map.toList (elimNN n)]

>         _                           -> singleFac (BinFac o `AppFac` m `AppFac` n)


Note that we cannot rewrite 0 ^ n to 0 because n might turn out to be 0 later!