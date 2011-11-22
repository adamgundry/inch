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
-}

module Units (Quantity, dimensionless, metres, seconds, grams,
                 minutes, hours, plus, minus, inv, times, over, scale,
                 kilo, centi, units) where


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

minutes = (.) (scale 60) seconds
hours   = (.) (scale 60) minutes


-- Arithmetic of units

plus :: Num a => Quantity u a -> Quantity u a -> Quantity u a
plus (Q x) (Q y) = Q (x + y)

minus :: Num a => Quantity u a -> Quantity u a -> Quantity u a
minus (Q x) (Q y) = Q (x - y)

inv :: forall (m s g :: Integer) a . Fractional a => 
           Quantity (Unit m s g) a -> Quantity (Unit (-m) (-s) (-g)) a
inv (Q x) = Q (recip x)

times :: forall (m s g m' s' g' :: Integer) a . Num a => 
             Quantity (Unit m s g) a -> Quantity (Unit m' s' g') a ->
                 Quantity (Unit (m + m') (s + s') (g + g')) a
times (Q x) (Q y) = Q (x * y)

over x y = times x (inv y)

scale :: Num a => a -> Quantity u a -> Quantity u a
scale x (Q y) = Q (x * y)

pow :: forall (m s g :: Integer) a . Fractional a =>
           pi (k :: Nat) . Quantity (Unit m s g) a ->
               Quantity (Unit (k * m) (k * s) (k * g)) a
pow {k} (Q x) = Q ((^^) x k)

sqr = pow {2}


-- We can write unit prefixes as transformers of the constructors...

kilo :: Num a => (a -> Quantity u a) -> a -> Quantity u a
kilo f x = scale 1000 (f x)

centi :: (Num a, Fractional a) => (a -> Quantity u a) -> a -> Quantity u a
centi f x = scale (recip 100) (f x)


-- ...allowing things like this:

kg = kilo grams
cm = centi metres


-- With a special name for flipped application, we can write
--     units 3 cm                                    for  0.03 m
--     units 15 (kilo metres) `over` units 3 hours   for  1.39 m/s

units :: a -> (a -> Quantity u b) -> Quantity u b
units x f = f x



-- distanceTravelled :: Fractional a => Quantity (Unit 0 1 0) a -> Quantity (Unit 1 0 0) a
-- or better yet Quantity Second a -> Quantity Metre a
-- or we can just omit the type annotations, and get good inference behaviour
distanceTravelled t = plus (times vel t) (times accel (sqr t))
  where
    vel    = over (units 2 metres) (units 1 seconds)
    accel  = over (units 36 metres) (sqr (units 10 seconds))


nastyExample x = let d = over x
                 in (d mass, d time)
  where
    mass = units 5 kg
    time = units 3 seconds