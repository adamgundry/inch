> module Num
>     (  GExp()
>     ,  mkGExp
>     ,  embedVar
>     ,  isIdentity
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
>     ,  substGExp
>     ,  negateGExp
>     ,  foldGExp
>     ) where

> import Data.Foldable (Foldable, find)
> import Data.List (sortBy, partition)
> import Data.Ord (comparing)
> import Data.Traversable (Traversable)

A group expression is represented as a |GExp| value with lists of
coefficients for the variables and constants; we maintain the
invariants that each variable or base unit occurs at most once, and
has a non-zero coefficient.

> data GExp b a = GExp [(a, Integer)] [(b, Integer)]
>     deriving Show

Unfortunately, there is no way to make the |Functor|, |Foldable| and
|Traversable| instances maintain the invariant, because it would
require restricting |fmap|, |foldMap| and |traverse| with |Eq|
typeclass constraints. Rather than inventing our own typeclasses, we
will manually ensure that we only call these methods with injective
functions.


To help maintain the invariant, we will use the |mkGExp| smart
constructor, which takes two arbitrary lists and combines the powers
of identical variables and base units.

> mkGExp :: (Eq a, Eq b) => [(a, Integer)] -> [(b, Integer)] -> GExp b a
> mkGExp vs bs = GExp (help vs []) (help bs [])
>   where
>     help :: Eq a => [(a, Integer)] -> [(a, Integer)] -> [(a, Integer)]
>     help []             ys = ys
>     help xs@((x, _):_)  ys = help xs' ys'
>       where
>         (as, xs')  = partition ((x ==) . fst) xs
>         n'         = sum (map snd as)
>         ys'        = if n' == 0 then ys else (x, n') : ys


We can also make a group expression consisting of a single variable
using |embedVar|.

> embedVar :: (Eq a, Eq b) => a -> GExp b a
> embedVar a = mkGExp [(a, 1)] []


Dimensions are compared for equality by sorting the lists:

> instance (Ord a, Ord b) => Eq (GExp b a) where
>   GExp vs1 bs1 == GExp vs2 bs2  = (sortFst vs1 == sortFst vs2)
>                                 && (sortFst bs1 == sortFst bs2)
>     where
>       sortFst :: Ord b => [(b, c)] -> [(b, c)]
>       sortFst = sortBy (comparing fst)


We provide utility functions to determine if a dimension is a unit or
constant, or the number of variables it contains.

> isIdentity :: GExp b a -> Bool
> isIdentity (GExp [] [])  = True
> isIdentity _             = False

> isConstant :: GExp b a -> Bool
> isConstant (GExp [] _)  = True
> isConstant _           = False

> getConstant :: GExp () a -> Maybe Integer
> getConstant (GExp [] [((), k)])  = Just k
> getConstant _                    = Nothing

> numVariables :: GExp b a -> Int
> numVariables (GExp vs _) = length vs


We also need versions of |find| and |lookup| that work on the list of
variables.

> findVariable :: ((a, Integer) -> Bool) -> GExp b a -> Maybe (a, Integer)
> findVariable p (GExp vs _) = find p vs

> lookupVariable :: Eq a => a -> GExp b a -> Maybe Integer
> lookupVariable a (GExp vs _) = lookup a vs


The |dividesCoeffs| function determines if an integer divides
all the coefficients of atoms in a dimension.

> dividesCoeffs :: Integer -> GExp b a -> Bool
> n `dividesCoeffs` (GExp vs bs) = dividesAll vs && dividesAll bs
>   where
>     dividesAll :: [(a, Integer)] -> Bool
>     dividesAll = all ((0 ==) . (`mod` n) . snd)


The |notMaxCoeff| function determines if the power of a variable is
less than the power of at least one other variable in a dimension.

> notMaxCoeff :: Eq a => (a, Integer) -> GExp b a -> Bool
> notMaxCoeff (alpha, n) (GExp vs _) = any bigger vs
>   where bigger (beta, m) = alpha /= beta && abs n <= abs m


The |(+~)| operator combines two group expressions by merging the
lists of variables and constants.

> (+~) :: (Eq a, Eq b) => GExp b a -> GExp b a -> GExp b a
> (GExp vs1 bs1) +~ (GExp vs2 bs2) = mkGExp (vs1 ++ vs2) (bs1 ++ bs2)

The |negateGExp| function negates the powers in a group expression.

> negateGExp :: (Eq a, Eq b) => GExp b a -> GExp b a
> negateGExp = mapCoeffs negate


> (-~) :: (Eq a, Eq b) => GExp b a -> GExp b a -> GExp b a
> d -~ e = d +~ negateGExp e

> (*~) :: (Eq a, Eq b) => Integer -> GExp b a -> GExp b a
> (*~) k = mapCoeffs (* k)

The |pivot| function removes the given variable (with its coefficient)
from the group expression, negates it and takes the quotient of its
coefficients by the coefficient of the removed variable.

> pivot :: (Eq a, Eq b) => (a, Integer) -> GExp b a -> GExp b a
> pivot (alpha, n) (GExp vs bs) = mapCoeffs (`quot` (-n)) $
>     GExp (deleteIndex alpha vs) bs


The |substGExp| function substitutes a group expression for a variable
(with its power) in another group expression.

> substGExp :: (Eq a, Eq b) => (a, Integer) -> GExp b a -> GExp b a -> GExp b a
> substGExp (alpha, n) d (GExp ws cs) =
>     mapCoeffs (n *) d +~ (GExp (deleteIndex alpha ws) cs)



> foldGExp :: (Integer -> a -> b -> b) -> (Integer -> b) -> GExp () a -> b
> foldGExp f g (GExp vs [((), m)]) = foldr (\ (a, n) -> f n a) (g m) vs
> foldGExp f g (GExp vs []) = foldr (\ (a, n) -> f n a) (g 0) vs


The following utility functions are just used within this module.

> mapCoeffs :: (Eq a, Eq b) => (Integer -> Integer) -> GExp b a -> GExp b a
> mapCoeffs f (GExp vs bs) = mkGExp (mapSnd vs) (mapSnd bs) 
>   where
>     mapSnd :: [(a, Integer)] -> [(a, Integer)]
>     mapSnd = map (\ (a, x) -> (a, f x))

> deleteIndex :: Eq a => a -> [(a, b)] -> [(a, b)]
> deleteIndex k = filter ((k /=) . fst) 



