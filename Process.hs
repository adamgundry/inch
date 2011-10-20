{-# OPTIONS_GHC -F -pgmF ./toy #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Process where

data Vec :: Num -> * -> * where
  VNil :: forall a . Vec 0 a
  VCons :: forall (n :: Num) a . 0 <= n => a -> Vec n a -> Vec (n+1) a

vhead :: forall a (m :: Num) . 0 < m => Vec m a -> a
vhead (VCons x xs) = x

rev :: forall a (m :: Nat) . Vec m a -> Vec m a
rev = let revapp :: forall (n k :: Nat) . Vec n a -> Vec k a -> Vec (n+k) a
          revapp xs VNil = xs
          revapp xs (VCons y ys) = revapp (VCons y xs) ys
      in revapp VNil

data Pro :: Num -> Num -> * -> * where
  Stop  :: forall a . Pro 0 0 a
  Say   :: forall (m n :: Num) a . 0 <= m, 0 <= n =>
               a -> Pro m n a -> Pro m (n+1) a
  Ask   :: forall (m n :: Num) a . 0 <= m, 0 <= n =>
               (a -> Pro m n a) -> Pro (m+1) n a

run :: forall (m n :: Num) a . Pro m n a -> Vec m a -> Vec n a
run Stop       VNil          = VNil
run (Say a p)  xs            = VCons a (run p xs)
run (Ask f)    (VCons x xs)  = run (f x) xs


sequ :: forall (m n i j :: Num) a . 0 <= n, 0 <= j =>
            Pro m i a -> Pro n j a -> Pro (m + n) (i + j) a
sequ Stop       q = q
sequ (Say b p)  q = Say b (sequ p q)
sequ (Ask f)    q = Ask (\ x -> sequ (f x) q)


pipe :: forall (m n i :: Num) a . 0 <= m =>
            Pro m n a -> Pro n i a -> Pro m i a
pipe p          Stop       = p
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

wires :: forall a. pi (n :: Num) . 0 <= n => Pro n n a
wires {0}   = Stop
wires {n+1} = sequ wire (wires {n})

manyWires = wires {1000}
sillyWires {n} = wires {1000000*n}

bind :: forall (m n j :: Num) a . 0 < n, 0 < j =>
            Pro m 1 a -> (a -> Pro n j a) -> Pro (m + n) j a 
bind (Say a p) g = sequ p (g a)
bind (Ask f)   g = Ask (\ x -> bind (f x) g)



v2i :: forall (n :: Num) . Vec n Bool -> Integer
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

toBin :: pi (m n :: Nat) . n < 2^m => Vec m Bool
toBin {0}   {n} = VNil
toBin {m+1} {n} = half {n} (\ {k} {r} -> VCons (odd' {r}) (toBin {m} {k}))

-- A real implementation of div/mod might be nice

divvy :: forall a. pi (n d :: Nat) . d >= 1 => (pi (m r :: Nat) . n ~ d * m + r, r < d => a) -> a
divvy {n}    {d} f | {n < d} = f {0} {n}
divvy {n}    {d} f | {n >= d} =
                     let g :: pi (m r :: Nat) . n - d ~ d * m + r, r < d => a
                         g {m} {r} = f {m+1} {r}
                     in divvy {n-d} {d} g


test :: forall (n :: Nat) . pi (m :: Nat) . Pro m n Bool ->
            (pi (k :: Nat) . k < 2 ^ m => Integer)
test {m} p {k} = v2i (rev (run p (rev (toBin {m} {k}))))


hadd :: Pro 2 2 Bool
hadd = pipe (sequ split split)
      (pipe (sequ wire (sequ cross wire))
            (sequ andGate xorGate))

fadd :: Pro 3 2 Bool
fadd = pipe (sequ hadd wire)
      (pipe (sequ wire hadd)
            (sequ wire orGate))
  