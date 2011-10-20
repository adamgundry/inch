{-# OPTIONS_GHC -F -pgmF ./toy #-}

{-# LANGUAGE GADTs, RankNTypes, KindSignatures, ScopedTypeVariables, NPlusKPatterns #-}

module NonlinearCost where

-- Abstraction barrier

data Cost :: Num -> * -> * where
  Hide :: forall (n :: Nat) a . a -> Cost n a

force :: forall (n :: Nat) a . Cost n a -> a
force (Hide a) = a

returnW :: forall (n :: Nat) a . a -> Cost n a
returnW = Hide

bind :: forall (m n :: Nat) a b . Cost m a ->
            (a -> Cost n b) -> Cost (m+n) b
bind (Hide x) f = Hide (force (f x))

weaken :: forall (n :: Nat) a . pi (m :: Nat) . Cost n a -> Cost (m + n) a
weaken {m} (Hide a) = Hide a

magicweak :: forall (m n :: Nat) a . m <= n => Cost m a -> Cost n a
magicweak (Hide a) = Hide a

-- End of abstraction barrier


ret :: forall a . a -> Cost 0 a
ret = returnW

return1 :: forall a . a -> Cost 1 a
return1 = returnW

join :: forall (m n :: Nat) a . Cost m (Cost n a) -> Cost (m + n) a
join m = bind m id

tick :: forall (n :: Nat) a . Cost n a -> Cost (n + 1) a
tick = weaken {1}

fmp :: forall (n :: Nat) a b . (a -> b) -> Cost n a -> Cost n b
fmp f x = bind x (\ x -> ret (f x))



data Proxy :: Num -> * where
  Proxy :: forall (n :: Num) . Proxy n

lemmaMulPos :: forall a (m n :: Nat) . Proxy m -> Proxy n -> (0 <= m * n => a) -> a
lemmaMulPos pm pn = lemmaMulPos pm pn


data BList :: * -> Num -> * where
  Nil  :: forall a (k :: Nat) . BList a k
  Cons :: forall a (k :: Nat) . a -> BList a k -> BList a (k+1)

wkBList :: forall a (m n :: Num) . m <= n => BList a m -> BList a n
wkBList Nil          = Nil
wkBList (Cons x xs)  = Cons x (wkBList xs)

filterB :: forall a (n :: Num) . (a -> Bool) -> BList a n -> Cost (n+1) (BList a n) 
filterB p Nil                       = tick (returnW Nil)
filterB p (Cons x xs)  | p x        = tick (fmp (Cons x) (filterB p xs))
                       | otherwise  = tick (fmp wkBList (filterB p xs))

nubByB :: forall a (n :: Num) . (a -> a -> Bool) -> BList a n ->
              Cost (n * (n + 3) + 1) (BList a n)
nubByB eq Nil          = lemmaMulPos (Proxy :: Proxy n) (Proxy :: Proxy n)
                           (tick (returnW Nil))
nubByB eq (Cons x xs)  = lemmaMulPos (Proxy :: Proxy (n-1)) (Proxy :: Proxy (n-1))
                           (tick (magicweak (bind (filterB (\ y -> not (eq x y)) xs)
                             (\ xs' -> tick (fmp (Cons x) (nubByB eq xs'))))))
