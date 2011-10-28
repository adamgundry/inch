{-# OPTIONS_GHC -F -pgmF inch #-}

{-# LANGUAGE GADTs, RankNTypes, KindSignatures, ScopedTypeVariables, NPlusKPatterns #-}

module NonlinearCost where

import Cost


data Proxy :: Num -> * where
  Proxy :: forall (n :: Num) . Proxy n


-- This should be implemented as the identity function, but we need
-- some way to pacify the type-checker. Even better, it should notice
-- that multiplication of naturals yields a natural number.

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
filterB p (Cons x xs)  | p x        = tick (mapCost (Cons x) (filterB p xs))
                       | otherwise  = tick (mapCost wkBList (filterB p xs))

nubByB :: forall a (n :: Num) . (a -> a -> Bool) -> BList a n ->
              Cost (n * (n + 3) + 1) (BList a n)
nubByB eq Nil          = lemmaMulPos (Proxy :: Proxy n) (Proxy :: Proxy n)
                           (tick (returnW Nil))
nubByB eq (Cons x xs)  = lemmaMulPos (Proxy :: Proxy (n-1)) (Proxy :: Proxy (n-1))
                           (tick (weaken (bindCost (filterB (\ y -> not (eq x y)) xs)
                             (\ xs' -> tick (mapCost (Cons x) (nubByB eq xs'))))))
