{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

{-
  An example of the need for type-level *integers* as well as natural
  numbers: representing units of measure. Quantites can only be added
  if the units match, and multiplication and division change the units
  appropriately. There is no runtime representation of units, and
  hence no runtime cost (at least there wouldn't be if Quantity was a
  newtype).

  See Bjorn Buckwalter's dimensional package
  (http://dimensional.googlecode.com/) for a more comprehensive
  implementation of this idea, using existing features of GHC Haskell.

  All this would be even cleaner if inch supported typeclasses, of
  course...
-}

module Units (Quantity, dimensionless, metres, seconds, grams,
                 minutes, hours, plus, minus, inv, times, over, scale,
                 kilo, centi, units) where

import Data.Ratio
import UnitsHacks


rat :: Integer -> Rational
rat k = (%) k 1



-- Unit collects indices for the powers of metres, seconds and grams
-- (other units are omitted for simplicity). Quantity has a phantom
-- type parameter which will usually be instantiated with some units,
-- but this allows us to write functions that are completely
-- polymorphic in the units very easily. Note that the Q constructor
-- should not be exported!

data Unit :: Integer -> Integer -> Integer -> * where

data Quantity :: * -> * -> * where
    Q :: forall a u . a -> Quantity u a
  deriving Show


-- If we had type synonyms, we could do this:

-- type Dimensionless    = Unit 0 0 0
-- type Metre            = Unit 1 0 0
-- type Second           = Unit 0 1 0
-- type Gram             = Unit 0 0 1
-- type MetresPerSecond  = Unit 1 (-1) 0
-- type Newton           = Unit 1 (-2) 1


-- Define some basic constructors

dimensionless :: a -> Quantity (Unit 0 0 0) a
dimensionless = Q

metres :: a -> Quantity (Unit 1 0 0) a
metres = Q

seconds :: a -> Quantity (Unit 0 1 0) a
seconds = Q

grams :: a -> Quantity (Unit 0 0 1) a
grams = Q

minutes x  = scale (rat 60) (seconds x)
hours x    = scale (rat 60) (minutes x)


-- Arithmetic of units (a bit annoying thanks to the lack of typeclass
-- support in the current version of inch, but otherwise straightforward)

plus :: Quantity u Rational -> Quantity u Rational -> Quantity u Rational
plus (Q x) (Q y) = Q (plusRational x y)

minus :: Quantity u Rational -> Quantity u Rational -> Quantity u Rational
minus (Q x) (Q y) = Q (minusRational x y)

inv :: forall (m s g :: Integer) . 
           Quantity (Unit m s g) Rational -> Quantity (Unit (-m) (-s) (-g)) Rational
inv (Q x) = Q (recipRational x)

times :: forall (m s g m' s' g' :: Integer) . 
             Quantity (Unit m s g) Rational -> Quantity (Unit m' s' g') Rational ->
                 Quantity (Unit (m + m') (s + s') (g + g')) Rational
times (Q x) (Q y) = Q (timesRational x y)

over x y = times x (inv y)

scale :: Rational -> Quantity u Rational -> Quantity u Rational
scale x (Q y) = Q (timesRational x y)

pow :: forall (m s g :: Integer) . pi (k :: Nat) .
           Quantity (Unit m s g) Rational ->
               Quantity (Unit (k * m) (k * s) (k * g)) Rational
pow {k} (Q x) = Q (powRational x k)

sqr = pow {2}


-- We can write unit prefixes as transformers of the constructors...

kilo :: (Rational -> Quantity u Rational) -> Rational -> Quantity u Rational
kilo f x = scale (rat 1000) (f x)

centi :: (Rational -> Quantity u Rational) -> Rational -> Quantity u Rational
centi f x = scale (recipRational (rat 100)) (f x)


-- ...allowing things like this:

kg = kilo grams
cm = centi metres


-- With a special name for flipped application, we can write
--     units 3 cm                                    for  0.03 m
--     units 15 (kilo metres) `over` units 3 hours   for  1.39 m/s

units :: a -> (a -> Quantity u b) -> Quantity u b
units x f = f x



-- distanceTravelled :: Quantity (Unit 0 1 0) Rational -> Quantity (Unit 1 0 0) Rational
-- or better yet Quantity Second Rational -> Quantity Metre Rational
-- or we can just omit the type annotations, and get good inference behaviour
distanceTravelled t = plus (times vel t) (times accel (sqr t))
  where
    vel    = over (metres (rat 2)) (seconds (rat 1))
    accel  = over (metres (rat 36)) (sqr (seconds (rat 10)))


nastyExample x = let d = over x
                 in (d mass, d time)
  where
    mass = units ((%) 5 6) kg
    time = units ((%) 3 2) seconds