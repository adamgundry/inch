{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Wires where

import Vectors


-- A value of type Wire m a n b represents a process that consumes m
-- inputs of type a and delivers n outputs of type b.

data Wire :: Nat -> * -> Nat -> * -> * where
  Stop  :: Wire 0 a 0 b
  Say   :: forall (m n :: Nat) a b .
               b -> Wire m a n b -> Wire m a (n+1) b
  Ask   :: forall (m n :: Nat) a b .
               (a -> Wire m a n b) -> Wire (m+1) a n b


-- Given a vector of inputs, we can run it to produce a vector of outputs

run :: forall (m n :: Nat) a b . Wire m a n b -> Vec a m -> Vec b n
run Stop       VNil          = VNil
run (Say a p)  xs            = VCons a (run p xs)
run (Ask f)    (VCons x xs)  = run (f x) xs


-- "Horizontal" composition of wires

sequ :: forall (m n i j :: Nat) a b .
            Wire m a i b -> Wire n a j b -> Wire (m + n) a (i + j) b
sequ Stop       q = q
sequ (Say b p)  q = Say b (sequ p q)
sequ (Ask f)    q = Ask (\ x -> sequ (f x) q)


-- "Vertical" composition of wires

pipe :: forall (m n i :: Nat) a b c .
            Wire m a n b -> Wire n b i c -> Wire m a i c
pipe Stop       Stop       = Stop
pipe (Ask f)    Stop       = Ask (\ x -> pipe (f x) Stop)
pipe p          (Say b q)  = Say b (pipe p q)
pipe (Say x p)  (Ask g)    = pipe p (g x)
pipe (Ask f)    (Ask g)    = Ask (\ x -> pipe (f x) (Ask g))


-- Some basic combinators and logic gates

always p = Ask (\ zzz -> p)

askB t f = Ask (bool t f)
  where
    bool t f True   = t
    bool t f False  = f

wire     = Ask (\ a -> Say a Stop)
notGate  = Ask (\ b -> Say (not b) Stop)
andGate  = askB wire (always (Say False Stop))
split    = Ask (\ a -> Say a (Say a Stop))
cross    = Ask (\ a -> Ask (\ b -> Say b (Say a Stop)))

mkGate tt tf ft ff = askB (askB (Say tt Stop) (Say tf Stop))
                          (askB (Say ft Stop) (Say ff Stop))

orGate    = mkGate True True True False
nandGate  = pipe andGate notGate
norGate   = pipe orGate notGate
xorGate   = askB notGate wire

wires :: forall a. pi (n :: Nat) . Wire n a n a
wires {0}   = Stop
wires {n+1} = sequ wire (wires {n})

manyWires = wires {1000}
sillyWires {n} = wires {1000000*n}

bind :: forall (m n j :: Nat) a . (0 < n, 0 < j) =>
            Wire m a 1 a -> (a -> Wire n a j a) -> Wire (m + n) a j a 
bind (Say a p) g = sequ p (g a)
bind (Ask f)   g = Ask (\ x -> bind (f x) g)


-- Half and full adders

hadd :: Wire 2 Bool 2 Bool
hadd = pipe (sequ split split)
      (pipe (sequ wire (sequ cross wire))
            (sequ andGate xorGate))

fadd :: Wire 3 Bool 2 Bool
fadd = pipe (sequ hadd wire)
      (pipe (sequ wire hadd)
            (sequ orGate wire))


-- Converting from multiple wires to vectors and vice versa

askVec :: forall a . pi (m :: Nat) . Wire m a 1 (Vec a m)
askVec = help VNil
  where
    help :: forall a (k :: Nat) . Vec a k -> (pi (m :: Nat) . Wire m a 1 (Vec a (m+k)))
    help xs {0}   = Say xs Stop
    help xs {m+1} = Ask (\ x -> help (VCons x xs) {m})

sayVec :: forall a b (k :: Nat) . Vec b k -> Wire 0 a k b
sayVec VNil          = Stop
sayVec (VCons x xs)  = Say x (sayVec xs)

bundle :: forall a. pi (m :: Nat) . Wire (2*m) a 2 (Vec a m)
bundle {m} = sequ (askVec {m}) (askVec {m})

unbundle :: forall a . pi (m :: Nat) . Wire 2 (Vec a m) (2*m) a
unbundle {m} = Ask (\ xs -> Ask (\ ys ->
                   sequ (sayVec (vreverse xs)) (sayVec (vreverse ys))))


-- Various bits and pieces to build a ripple-carry adder recursively

crosses :: forall a . pi (k :: Nat) . Wire (4 * k) a (4 * k) a
crosses {k} = pipe (sequ (bundle {k}) (bundle {k}))
                  (pipe (sequ wire (sequ cross wire))
                        (sequ (unbundle {k}) (unbundle {k})))

ripple :: forall a . pi (m :: Nat) .
              Wire (2 * 2 ^ m + 1) a (1 + 2 ^ m) a ->
                  Wire (2 * 2 ^ (m+1) + 1) a (1 + 2 ^ (m+1)) a
ripple {m} add | {0 <= 2 ^ m} = pipe (sequ (crosses {2 ^ m}) wire)
                                   (pipe (sequ (wires {2 ^ (m+1)}) add)
                                         (sequ add (wires {2 ^ m})))

adder :: pi (m :: Nat) . Wire (2 * 2 ^ m + 1) Bool (1 + 2 ^ m) Bool
adder {0}    = fadd
adder {m+1}  = ripple {m} (adder {m})


-- We don't have type-level div/mod (yet?) but can fake it thus

divvy :: forall a. pi (n d :: Nat) . 1 <= d =>
             (pi (m r :: Nat) . (n ~ d * m + r, r < d) => a) -> a
divvy {n}    {d} f | {n < d} = f {0} {n}
divvy {n}    {d} f | {n >= d} =
                     let g :: pi (m r :: Nat) . (n - d ~ d * m + r, r < d) => a
                         g {m} {r} = f {m+1} {r}
                     in divvy {n-d} {d} g

half :: forall a. pi (n :: Nat) . (pi (m r :: Nat) . (n ~ 2 * m + r, r <= 1) => a) -> a
half {n} = divvy {n} {2}


-- integerToBin {m} {n} is the m-bit unsigned binary representation of
-- the number n; the type guarantees that n is in the range [0..2^m-1]

integerToBin :: pi (m n :: Nat) . n < 2^m => Vec Bool m
integerToBin {m} {n} = vreverse (toBin {m} {n})
  where
    toBin :: pi (m n :: Nat) . n < 2^m => Vec Bool m
    toBin {0}   {n} = VNil
    toBin {m+1} {n} = half {n} (\ {k} {r} -> VCons (odd r) (toBin {m} {k}))


-- binToInteger converts an n-bit unsigned binary number (represented as a
-- vector of booleans) to the corresponding integer

binToInteger :: forall (n :: Nat) . Vec Bool n -> Integer
binToInteger xs = fromBin (vreverse xs)
  where
    fromBin :: forall (n :: Nat) . Vec Bool n -> Integer
    fromBin VNil = 0
    fromBin (VCons True xs) = 1 + (2 * (fromBin xs))
    fromBin (VCons False xs) = 2 * (fromBin xs)


-- binToString converts a vector of booleans to a string
-- representation of the corresponding binary number

binToString xs = map btoc (vec2list xs)
  where
    btoc True   = '1'
    btoc False  = '0'

-- test :: forall (n :: Nat) . pi (m :: Nat) . Wire m Bool n Bool ->
--             (pi (k :: Nat) . k < 2 ^ m => [Char])
test  {m} p {k} = binToString  (run p (integerToBin {m} {k}))
test' {m} p {k} = binToInteger (run p (integerToBin {m} {k}))


-- Calculate 01 + 11 + 0 = 100 (note that 01110bin = 13dec)
calc1 = test {5} (adder {1}) {13}

-- Calculate 0101 + 1100 + 1 = 10010 (note that 010111001bin = 185dec)
calc2 = test {9} (adder {2}) {185}



-- "Horizontal" k-fold repetition of wires requires multiplication. At
-- the moment we have to supply a lemma (operationally the identity
-- function) that proves that a product of positive numbers is
-- positive. A proxy is used as a substitute for type application.

data Proxy :: Integer -> * where
  Proxy :: forall (n :: Integer) . Proxy n

nsequ :: forall (m n :: Nat) a b .
           (forall (x y :: Nat) t . Proxy x -> Proxy y ->
                                        (0 <= x * y => t) -> t) ->
             (pi (k :: Nat) . Wire m a n b -> Wire (m * k) a (n * k) b)
nsequ lem {0}    p = Stop
nsequ lem {k+1}  p = lem (Proxy :: Proxy m) (Proxy :: Proxy k)
                    (lem (Proxy :: Proxy n) (Proxy :: Proxy k)
                        (sequ p (nsequ lem {k} p)))
