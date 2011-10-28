{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Wires where

import Vectors

data Wire :: Num -> * -> Num -> * -> * where
  Stop  :: Wire 0 a 0 b
  Say   :: forall (m n :: Nat) a b .
               b -> Wire m a n b -> Wire m a (n+1) b
  Ask   :: forall (m n :: Nat) a b .
               (a -> Wire m a n b) -> Wire (m+1) a n b

run :: forall (m n :: Num) a b . Wire m a n b -> Vec a m -> Vec b n
run Stop       VNil          = VNil
run (Say a p)  xs            = VCons a (run p xs)
run (Ask f)    (VCons x xs)  = run (f x) xs


sequ :: forall (m n i j :: Num) a b . 0 <= n, 0 <= j =>
            Wire m a i b -> Wire n a j b -> Wire (m + n) a (i + j) b
sequ Stop       q = q
sequ (Say b p)  q = Say b (sequ p q)
sequ (Ask f)    q = Ask (\ x -> sequ (f x) q)


data Proxy :: Num -> * where
  Proxy :: forall (n :: Num) . Proxy n

nsequ :: forall (m n :: Nat) a b .
           (forall (x y :: Nat) t . Proxy x -> Proxy y -> (0 <= x * y => t) -> t) ->
             (pi (k :: Nat) . Wire m a n b -> Wire (m * k) a (n * k) b)
nsequ lem {0}    p = Stop
nsequ lem {k+1}  p = lem (Proxy :: Proxy m) (Proxy :: Proxy k)
                    (lem (Proxy :: Proxy n) (Proxy :: Proxy k)
                        (sequ p (nsequ lem {k} p)))


pipe :: forall (m n i :: Num) a b c . 0 <= m =>
            Wire m a n b -> Wire n b i c -> Wire m a i c
pipe Stop       Stop       = Stop
pipe (Ask f)    Stop       = Ask (\ x -> pipe (f x) Stop)
pipe p          (Say b q)  = Say b (pipe p q)
pipe (Say x p)  (Ask g)    = pipe p (g x)
pipe (Ask f)    (Ask g)    = Ask (\ x -> pipe (f x) (Ask g))

always p = Ask (\ zzz -> p)

bool t f True   = t
bool t f False  = f

askB t f = Ask (bool t f)

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

wires :: forall a. pi (n :: Num) . 0 <= n => Wire n a n a
wires {0}   = Stop
wires {n+1} = sequ wire (wires {n})

manyWires = wires {1000}
sillyWires {n} = wires {1000000*n}

bind :: forall (m n j :: Num) a . 0 < n, 0 < j =>
            Wire m a 1 a -> (a -> Wire n a j a) -> Wire (m + n) a j a 
bind (Say a p) g = sequ p (g a)
bind (Ask f)   g = Ask (\ x -> bind (f x) g)



v2i :: forall (n :: Num) . Vec Bool n -> Integer
v2i VNil = 0
v2i (VCons True xs) = 1 + (2 * (v2i xs))
v2i (VCons False xs) = 2 * (v2i xs)


odd' :: pi (n :: Nat) . Bool
odd' {0}    = False
odd' {n+1}  = not (odd' {n})

half :: forall a. pi (n :: Nat) . (pi (m r :: Nat) . n ~ 2 * m + r, r <= 1 => a) -> a
half {0}    f = f {0} {0} 
half {n+1}  f = let
                  g :: pi (m r :: Nat) . n ~ 2 * m + r, r <= 1 => a
                  g {m} {0} = f {m} {1}
                  g {m} {1} = f {m+1} {0}
                in half {n} g

-- This needs 2^(x + y)  ~>  2^x * 2^y

toBin' :: pi (m n :: Nat) . n < 2^m => Vec Bool m
toBin' {0}   {n} = VNil
toBin' {m+1} {n} = half {n} (\ {k} {r} -> VCons (odd' {r}) (toBin' {m} {k}))

toBin :: pi (m n :: Nat) . n < 2^m => Vec Bool m
toBin {m} {n} = vreverse (toBin' {m} {n})

-- A real implementation of div/mod might be nice

divvy :: forall a. pi (n d :: Nat) . d >= 1 => (pi (m r :: Nat) . n ~ d * m + r, r < d => a) -> a
divvy {n}    {d} f | {n < d} = f {0} {n}
divvy {n}    {d} f | {n >= d} =
                     let g :: pi (m r :: Nat) . n - d ~ d * m + r, r < d => a
                         g {m} {r} = f {m+1} {r}
                     in divvy {n-d} {d} g


test :: forall (n :: Nat) . pi (m :: Nat) . Wire m Bool n Bool ->
            (pi (k :: Nat) . k < 2 ^ m => Integer)
test {m} p {k} = v2i (vreverse (run p (toBin {m} {k})))


hadd :: Wire 2 Bool 2 Bool
hadd = pipe (sequ split split)
      (pipe (sequ wire (sequ cross wire))
            (sequ andGate xorGate))

fadd :: Wire 3 Bool 2 Bool
fadd = pipe (sequ hadd wire)
      (pipe (sequ wire hadd)
            (sequ orGate wire))
  

askVec :: forall a . pi (m :: Nat) . Wire m a 1 (Vec a m)
askVec = let help :: forall a (k :: Nat) . Vec a k -> (pi (m :: Nat) . Wire m a 1 (Vec a (m+k)))
             help xs {0}   = Say xs Stop
             help xs {m+1} = Ask (\ x -> help (VCons x xs) {m})
         in help VNil

sayVec :: forall a b (k :: Num) . Vec b k -> Wire 0 a k b
sayVec VNil          = Stop
sayVec (VCons x xs)  = Say x (sayVec xs)

bundle2 :: forall a. pi (m :: Nat) . Wire (2*m) a 2 (Vec a m)
bundle2 {m} = sequ (askVec {m}) (askVec {m})

unbundle2 :: forall a . pi (m :: Nat) . Wire 2 (Vec a m) (2*m) a
unbundle2 {m} = Ask (\ xs -> Ask (\ ys -> sequ (sayVec (vreverse xs)) (sayVec (vreverse ys))))


fizz = pipe (bundle2 {3}) (unbundle2 {3})



crosses :: forall a . pi (k :: Nat) . Wire (2 * k) a (2 * k) a
crosses {k} = pipe (bundle2 {k})
             (pipe cross
                   (unbundle2 {k}))

crosses' :: forall a .
              (forall (x y :: Nat) t . Proxy x -> Proxy y -> (0 <= x * y => t) -> t) ->
                (pi (k :: Nat) . Wire (4 * k) a (4 * k) a)
crosses' lem {k} = pipe (nsequ lem {2} (bundle2 {k}))
                  (pipe (sequ wire (sequ cross wire))
                        (nsequ lem {2} (unbundle2 {k})))



ripple :: forall a .
            (forall (x y :: Nat) t . Proxy x -> Proxy y -> (0 <= x * y => t) -> t) ->
            (pi (m :: Nat) . Wire (2 * 2 ^ m + 1) a (1 + 2 ^ m) a ->
                                 Wire (2 * 2 ^ (m+1) + 1) a (1 + 2 ^ (m+1)) a)
ripple lem {m} add | {0 <= 2 ^ m} = pipe (sequ (crosses' lem {2 ^ m}) wire)
                                   (pipe (sequ (wires {2 ^ (m+1)}) add)
                                         (sequ add (wires {2 ^ m})))

adder :: (forall (x y :: Nat) t . Proxy x -> Proxy y -> (0 <= x * y => t) -> t) ->
             (pi (m :: Nat) . Wire (2 * 2 ^ m + 1) Bool (1 + 2 ^ m) Bool)
adder lem {0}    = fadd
adder lem {m+1}  = ripple lem {m} (adder lem {m})




btoc True   = '1'
btoc False  = '0'

vtol :: forall a (n :: Num) . Vec a n -> [a]
vtol VNil          = []
vtol (VCons x xs)  = x : vtol xs

vtob xs = map btoc (vtol xs)

test' {m} p {k} = vtob (run p (toBin {m} {k}))