{-# OPTIONS_GHC -F -pgmF ./toy #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Process where

data Vec :: Num -> * -> * where
  VNil :: forall a . Vec 0 a
  VCons :: forall (n :: Num) a . 0 <= n => a -> Vec n a -> Vec (n+1) a

vhead :: forall a (m :: Num) . 0 < m => Vec m a -> a
vhead (VCons x xs) = x

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

askB t f = let fi t f True  = t
               fi t f False = f
           in Ask (fi t f)

wire     = Ask (\ a -> Say a Stop)
notGate  = askB (Say False Stop) (Say True Stop)
andGate  = askB wire (always (Say False Stop))

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


bind :: forall (m n j :: Num) a . 0 < n, 0 < j =>
            Pro m 1 a -> (a -> Pro n j a) -> Pro (m + n) j a 
bind (Say a p) g = sequ p (g a)
bind (Ask f)   g = Ask (\ x -> bind (f x) g)



v2i :: forall a (n :: Num) . a -> (a -> a) -> (a -> a) -> Vec n Bool -> a
v2i o s d VNil = o
v2i o s d (VCons True xs) = s (d (v2i o s d xs))
v2i o s d (VCons False xs) = d (v2i o s d xs)