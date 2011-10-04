> {-# LANGUAGE GADTs, TypeSynonymInstances #-}

> module TyNum where

> import Control.Applicative
> import Data.Traversable
> import Data.List

> import Debug.Trace

> import Kind
> import Type

> data NormNum a where
>     NN :: Integer -> [(Var a KNum, Integer)] -> [(Ty a KNum, Integer)] -> NormNum a
>   deriving (Eq, Show)

> type NormalNum        = NormNum ()
> type NormPred a       = Pred (NormNum a)
> type NormalPredicate  = Pred NormalNum

> instance Num (NormNum a) where
>     fromInteger i             = NN i [] []
>
>     NN i as ts  + NN j bs us  = NN (i+j) (combine (as ++ bs)) (combine (ts ++ us))
>
>     negate (NN i as ts)       = NN (-i) (mapSnd negate as) (mapSnd negate ts)
>
>     NN i [] []  * n           = i *~ n
>     n           * NN j [] []  = j *~ n
>     NN i as ts  * NN j bs us  = mkNormNum $ cprod ((TyInt i, 1) : mapFst TyVar as ++ ts)
>                                                   ((TyInt j, 1) : mapFst TyVar bs ++ us)

> cprod :: [(Ty a KNum, Integer)] -> [(Ty a KNum, Integer)] -> [(Ty a KNum, Integer)]
> cprod xs ys = [mk t u (i * j) | (t, i) <- xs, (u, j) <- ys]
>   where
>     mk (TyInt i) (TyInt j) k = (TyInt (i*j*k), 1)
>     mk (TyInt i) t         k = (t, i*k)
>     mk t         (TyInt j) k = (t, j*k)
>     mk t         u         k = (t * u, k)

> mkNormNum :: [(Ty a KNum, Integer)] -> NormNum a
> mkNormNum []                   = 0
> mkNormNum ((TyInt i, j) : ts)  = fromInteger (i*j) + mkNormNum ts
> mkNormNum ((TyVar a, j) : ts)  = NN 0 [(a, j)] [] + mkNormNum ts
> mkNormNum ((t, j) : ts)        = NN 0 [] [(t, j)] + mkNormNum ts

> (*~) :: Integer -> NormNum a -> NormNum a
> 0 *~ _           = 0
> 1 *~ n           = n
> i *~ NN j bs us  = NN (i*j) (mapSnd (i*) bs) (mapSnd (i*) us)




> mapFst :: (a -> b) -> [(a, c)] -> [(b, c)]
> mapFst f = map (\ (x, c) -> (f x, c))

> mapSnd :: (b -> c) -> [(a, b)] -> [(a, c)]
> mapSnd f = map (\ (a, x) -> (a, f x))

> getConstant :: NormNum a -> Maybe Integer
> getConstant (NN i [] [])  = Just i
> getConstant _             = Nothing

> isZero :: NormNum a -> Bool
> isZero = (== Just 0) . getConstant

> combine :: Eq a => [(a, Integer)] -> [(a, Integer)]
> combine xs = help xs []
>   where
>     help []             ys = ys
>     help xs@((x, _):_)  ys = help xs' ys'
>       where
>         (as, xs')  = partition ((x ==) . fst) xs
>         n'         = sum (map snd as)
>         ys'        = if n' == 0 then ys else (x, n') : ys

> mkVar :: Var a KNum -> NormNum a
> mkVar a = NN 0 [(a, 1)] []

> numVariables :: NormNum a -> Int
> numVariables (NN _ as _) = length as

> substNum :: Var () KNum -> Type KNum -> NormalNum -> NormalNum
> substNum a t n = normaliseNum (replaceTy a t (reifyNum n))


> data SolveResult t where
>     Absent    :: SolveResult t
>     Solve     :: t -> SolveResult t
>     Simplify  :: t -> SolveResult t
>     Stuck     :: SolveResult t
>   deriving Show

> solveFor :: Var () KNum -> NormalNum -> SolveResult NormalNum
> solveFor a (NN i as ts) = case (lookup a as, a <? map fst ts) of
>     (Nothing,  False) -> Absent
>     (Just n,   False)
>       | all ((n `divides`)) (map snd as ++ map snd ts)  -> Solve t
>       | notMaxCoeff (a, n) as                           -> Simplify t
>       where t = NN (q i) (combine (mapSnd q (filter ((a /=) . fst) as)))
>                          (combine (mapSnd q ts))
>             q x = x `quot` (-n)
>     _ -> Stuck
>   where
>     n `divides` m = m `mod` n == 0
>     notMaxCoeff (a, n) = any (bigger (a, n))
>     bigger (a, n) (b, m) = a /= b && abs n <= abs m

> maybeSolveFor :: Var () KNum -> NormalNum -> Maybe NormalNum
> maybeSolveFor a t = case solveFor a t of
>                         Solve t  -> Just t
>                         _        -> Nothing


> partitionNum :: [Var () KNum] -> NormalNum -> (NormalNum, NormalNum)
> partitionNum vs (NN i as ts) = (NN 0 las lts, NN i ras rts)
>   where
>     (las, ras) = help as [] []
>     (lts, rts) = help ts [] []

>     help ::  FV f => [(f, Integer)] -> [(f, Integer)] -> [(f, Integer)] ->
>                  ([(f, Integer)], [(f, Integer)])
>     help [] ls rs = (ls, rs)
>     help ((x, n):xns) ls rs | any (<? x) vs  = help xns ((x, n):ls) rs
>                             | otherwise      = help xns ls ((x, n):rs)




> reifyNum :: NormNum a -> Ty a KNum
> reifyNum (NN i as ts) = tySum pos -~ tySum neg
>   where
>     tySum :: [(Ty a KNum, Integer)] -> Ty a KNum
>     tySum = foldr (\ (t, k) u -> (k *** t) +++ u) 0

>     pos = (if i > 0 then [(TyInt i, 1)] else []) ++ map (\ (a, k) -> (TyVar a, k)) posAs ++ posTs
>     neg = (if i < 0 then [(TyInt (-i), 1)] else []) ++ map (\ (a, k) -> (TyVar a, -k)) negAs ++ mapSnd negate negTs
>     (posAs, negAs) = partition ((> 0) . snd) as
>     (posTs, negTs) = partition ((> 0) . snd) ts
>     
>     (+++) :: Ty a KNum -> Ty a KNum -> Ty a KNum
>     TyInt i  +++ TyInt j  = TyInt (i + j)
>     TyInt 0  +++ t        = t
>     t        +++ TyInt 0  = t
>     t        +++ t'       = t + t'

>     (***) :: Integer -> Ty a KNum -> Ty a KNum
>     i        *** TyInt j  = TyInt (i * j)
>     0        *** t        = TyInt 0
>     1        *** t        = t
>     k        *** t        = TyInt k * t

>     (-~) :: Ty a KNum -> Ty a KNum -> Ty a KNum
>     TyInt i  -~ TyInt j   = TyInt (i - j)
>     t        -~ TyInt 0   = t
>     t        -~ t'        = t - t'

> {-
> reifyNum (NN i as ts) = TyInt i +++ foldr (\ (a, k) t -> (k *** TyVar a) +++ t) 0 as +++ foldr (\ (t, k) t' -> (k *** t) +++ t') 0 ts
>   where
>     TyInt 0  +++ t        = t
>     t        +++ TyInt 0  = t
>     t        +++ t'       = t + t'

>     0        *** t        = TyInt 0
>     1        *** t        = t
>     k        *** t        = TyInt k * t
> -}

> reifyPred :: Pred (NormNum a) -> Pred (Ty a KNum)
> reifyPred = fmap reifyNum

> normaliseNum :: Ty a KNum -> NormNum a
> normaliseNum (TyInt i)     = fromInteger i
> normaliseNum (TyVar a)     = mkVar a
> normaliseNum t@(TyApp (TyApp (BinOp o) m) n) =
>     let m' = normaliseNum m
>         n' = normaliseNum n
>     in case (o, getConstant m', getConstant n') of
>         (o,      Just i,   Just j)  -> fromInteger (binOpFun o i j)
>         (Plus,   _,        _)       -> m' + n'
>         (Minus,  _,        _)       -> m' - n'
>         (Times,  _,        _)       -> m' * n'
>         _                           -> NN 0 [] [(t, 1)]
> normaliseNum t = NN 0 [] [(t, 1)]

> normalisePred :: Pred (Ty a KNum) -> NormPred a
> normalisePred = fmap normaliseNum


> trivialPred :: Ord a => Pred (Ty a KNum) -> Maybe Bool
> trivialPred (P c m n)     = compFun c 0 <$> (getConstant (normaliseNum (n - m)))
> trivialPred (Op o m n t)  = (== 0) <$> (getConstant (normaliseNum (binOp o m n - t)))
