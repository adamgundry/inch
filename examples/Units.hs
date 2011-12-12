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

module Units (Quantity, dimensionless, metres, seconds, kilograms,
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


type Dimensionless     = Unit 0 0 0
type Metres            = Unit 1 0 0
type Seconds           = Unit 0 1 0
type Kilograms         = Unit 0 0 1
type MetresPerSecond   = Unit 1 (-1) 0
type Newtons           = Unit 1 (-2) 1


-- Define some basic constructors

dimensionless :: a -> Quantity Dimensionless a
dimensionless = Q

metres :: a -> Quantity Metres a
metres = Q

seconds :: a -> Quantity Seconds a
seconds = Q

kilograms :: a -> Quantity Kilograms a
kilograms = Q

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

type Prefix u a = (a -> Quantity u a) -> a -> Quantity u a

prefix :: Num a => a -> Prefix u a
prefix n f x = scale n (f x)

kilo = prefix 1000
centi = prefix (recip 100)
milli = prefix (recip 1000)

-- ...allowing things like this:

km  = kilo metres
cm  = centi metres
mm  = milli metres
g   = milli kilograms


-- With a special name for flipped application, we can write
--     units 3 cm                                    for  0.03 m
--     units 15 (kilo metres) `over` units 3 hours   for  1.39 m/s

units :: a -> (a -> Quantity u b) -> Quantity u b
units x f = f x



-- distanceTravelled :: (Num a, Fractional a) => Quantity Seconds a -> Quantity Metres a
-- or we can just omit the type annotations, and get good inference behaviour
distanceTravelled t = plus (times vel t) (times accel (sqr t))
  where
    vel    = over (units 2 metres) (units 1 seconds)
    accel  = over (units 36 metres) (sqr (units 10 seconds))


-- This is Kennedy's example of a function whose type cannot be
-- inferred by the units-of-measure type system in F#, because of
-- difficulties with generalisation (see Kennedy, Types for
-- Units-of-Measure: Theory and Practice, 2009, section 3.10).

nastyExample = \ x -> let d = div x
                      in (d mass, d time)
  where
    div = over
    mass = units 5 kilograms
    time = units 3 seconds