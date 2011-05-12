> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Num
>     (  NExp()
>     ,  mkNExp
>     ,  mkVar
>     ,  mkConstant
>     ,  isZero
>     ,  isConstant
>     ,  getConstant
>     ,  numVariables
>     ,  findVariable
>     ,  lookupVariable
>     ,  dividesCoeffs
>     ,  notMaxCoeff
>     ,  (+~)
>     ,  (-~)
>     ,  (*~)
>     ,  pivot
>     ,  bindNExp
>     ,  substNExp
>     ,  substNum
>     ,  negateNExp
>     ,  foldNExp
>     ,  solveForVar
>     ,  partitionNExp
>     ) where

> import Data.Foldable (Foldable, find)
> import Data.List (sortBy, partition)
> import Data.Ord (comparing)
> import Data.Traversable (Traversable)

A numeric expression is represented as a list of coefficients for the
variables and a constant; we maintain the invariants that each
variable occurs at most once, and has a non-zero coefficient.

> data NExp a = NExp [(a, Integer)] Integer
>     deriving (Functor, Foldable, Traversable, Show)

Unfortunately, there is no way to make the |Functor|, |Foldable| and
|Traversable| instances maintain the invariant, because it would
require restricting |fmap|, |foldMap| and |traverse| with |Eq|
typeclass constraints. Rather than inventing our own typeclasses, we
will manually ensure that we only call these methods with injective
functions.

To help maintain the invariant, we will use the |mkNExp| smart
constructor, which takes two arbitrary lists and combines the powers
of identical variables and base units.

> mkNExp :: Eq a => [(a, Integer)] -> Integer -> NExp a
> mkNExp vs b = NExp (help vs []) b
>   where
>     help :: Eq a => [(a, Integer)] -> [(a, Integer)] -> [(a, Integer)]
>     help []             ys = ys
>     help xs@((x, _):_)  ys = help xs' ys'
>       where
>         (as, xs')  = partition ((x ==) . fst) xs
>         n'         = sum (map snd as)
>         ys'        = if n' == 0 then ys else (x, n') : ys


We can also make a group expression consisting of a single variable
using |mkVar|, and a single constant using |mkConst|.

> mkVar :: Eq a => a -> NExp a
> mkVar a = mkNExp [(a, 1)] 0

> mkConstant :: Integer -> NExp a
> mkConstant = NExp []


Numeric expressions are compared for equality by sorting the lists:

> instance Ord a => Eq (NExp a) where
>   NExp xs k == NExp ys l = (sortFst xs == sortFst ys) && k == l
>     where
>       sortFst :: Ord b => [(b, c)] -> [(b, c)]
>       sortFst = sortBy (comparing fst)


We provide utility functions to determine if a dimension is a unit or
constant, or the number of variables it contains.

> isZero :: NExp a -> Bool
> isZero (NExp [] 0)  = True
> isZero _            = False

> isConstant :: NExp a -> Bool
> isConstant (NExp [] _)  = True
> isConstant _           = False

> getConstant :: NExp a -> Maybe Integer
> getConstant (NExp [] n)  = Just n
> getConstant _            = Nothing

> numVariables :: NExp a -> Int
> numVariables (NExp vs _) = length vs


We also need versions of |find| and |lookup| that work on the list of
variables.

> findVariable :: ((a, Integer) -> Bool) -> NExp a -> Maybe (a, Integer)
> findVariable p (NExp vs _) = find p vs

> lookupVariable :: Eq a => a -> NExp a -> Maybe Integer
> lookupVariable a (NExp vs _) = lookup a vs


The |dividesCoeffs| function determines if an integer divides
all the coefficients of atoms in a dimension.

> dividesCoeffs :: Integer -> NExp a -> Bool
> n `dividesCoeffs` (NExp vs b) = dividesAll vs && divides b
>   where
>     divides     = (0 ==) . (`mod` n)
>     dividesAll  = all (divides . snd)


The |notMaxCoeff| function determines if the power of a variable is
less than the power of at least one other variable in a dimension.

> notMaxCoeff :: Eq a => (a, Integer) -> NExp a -> Bool
> notMaxCoeff (alpha, n) (NExp vs _) = any bigger vs
>   where bigger (beta, m) = alpha /= beta && abs n <= abs m


The |(+~)| operator combines two group expressions by merging the
lists of variables and constants.

> (+~) :: Eq a => NExp a -> NExp a -> NExp a
> (NExp xs k) +~ (NExp ys l) = mkNExp (xs ++ ys) (k + l)

The |negateNExp| function negates the powers in a group expression.

> negateNExp :: Eq a => NExp a -> NExp a
> negateNExp = mapCoeffs negate


> (-~) :: Eq a => NExp a -> NExp a -> NExp a
> d -~ e = d +~ negateNExp e

> (*~) :: Eq a => Integer -> NExp a -> NExp a
> (*~) k = mapCoeffs (* k)

The |pivot| function removes the given variable (with its coefficient)
from the group expression, negates it and takes the quotient of its
coefficients by the coefficient of the removed variable.

> pivot :: Eq a => (a, Integer) -> NExp a -> NExp a
> pivot (alpha, n) (NExp vs b) = mapCoeffs (`quot` (-n)) $
>     NExp (deleteIndex alpha vs) b


> bindNExp :: (Eq a, Eq b) => (a -> NExp b) -> NExp a -> NExp b
> bindNExp f (NExp xs k) = foldr (+~) (mkConstant k) $
>                              map (\ (a, n) -> n *~ f a) xs

The |substNExp| function substitutes a group expression for a variable
(with its power) in another group expression.

> substNExp :: Eq a => (a, Integer) -> NExp a -> NExp a -> NExp a
> substNExp (alpha, n) d (NExp ws k) =
>     mapCoeffs (n *) d +~ (NExp (deleteIndex alpha ws) k)


> substNum ::  Eq a => a -> NExp a -> NExp a -> NExp a
> substNum alpha d e = case lookupVariable alpha e of
>     Just n   -> substNExp (alpha, n) d e
>     Nothing  -> e


> foldNExp :: (Integer -> a -> b -> b) -> (Integer -> b) -> NExp a -> b
> foldNExp f g (NExp vs m) = foldr (\ (a, n) -> f n a) (g m) vs



> solveForVar :: Eq a => a -> NExp a -> Maybe (NExp a)
> solveForVar a n = case lookupVariable a n of
>     Just i | i `dividesCoeffs` n  -> Just (pivot (a, i) n)
>     _                             -> Nothing



> partitionNExp :: Eq a => [a] -> NExp a -> (NExp a, NExp a)
> partitionNExp as (NExp vs k) = help vs [] []
>   where
>     help [] ls rs = (mkNExp ls 0, mkNExp rs k)
>     help ((a, n):vs) ls rs | a `elem` as  = help vs ((a, n):ls) rs
>                            | otherwise    = help vs ls ((a, n):rs)


The following utility functions are just used within this module.

> mapCoeffs :: Eq a => (Integer -> Integer) -> NExp a -> NExp a
> mapCoeffs f (NExp vs k) = mkNExp (mapSnd vs) (f k)
>   where
>     mapSnd :: [(a, Integer)] -> [(a, Integer)]
>     mapSnd = map (\ (a, x) -> (a, f x))

> deleteIndex :: Eq a => a -> [(a, b)] -> [(a, b)]
> deleteIndex k = filter ((k /=) . fst) 



