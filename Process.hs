{-# OPTIONS_GHC -F -pgmF ./toy #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Process where

data Vec :: Num -> * -> * where
  VNil :: forall (n :: Num) a . n ~ 0 => Vec n a
  VCons :: forall (n m :: Num) a . 1 <= n => a -> Vec (n-1) a -> Vec n a

vhead :: forall a (m :: Num) . 0 < m => Vec m a -> a
vhead (VCons x xs) = x

data Pro :: Num -> Num -> * -> * where
  Stop  :: forall (m n :: Num) a . m ~ 0, n ~ 0 =>
               Pro m n a
  Say   :: forall (m n :: Num) a . 0 <= m, 0 < n =>
               a -> Pro m (n-1) a -> Pro m n a
  Ask   :: forall (m n :: Num) a . 0 < m, 0 <= n =>
               (a -> Pro (m-1) n a) -> Pro m n a

run :: forall (m n :: Num) a . Pro m n a -> Vec m a -> Vec n a
run Stop       VNil          = VNil
run (Say a p)  xs            = VCons a (run p xs)
run (Ask f)    (VCons x xs)  = run (f x) xs


sequ :: forall (m n i j :: Num) a . 0 < n, 0 < j =>
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


fi t f True  = t
fi t f False = f

askB t f = Ask (fi t f)

wire     = askB (Say True Stop) (Say False Stop)
notGate  = askB (Say False Stop) (Say True Stop)

always p = Ask (\ zzz -> p)

andGate = askB wire (always (Say False Stop))



bind :: forall (m n j :: Num) a . 0 < n, 0 < j =>
            Pro m 1 a -> (a -> Pro n j a) -> Pro (m + n) j a 
bind (Say a p) g = sequ p (g a)
bind (Ask f)   g = Ask (\ x -> bind (f x) g)