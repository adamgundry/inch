{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Induction where

induction :: forall (f :: Num -> *) . pi (m :: Nat) . f 0 -> (forall (n :: Nat) . f n -> f (n+1)) -> f m
induction {0} z s = z
induction {m+1} z s = s (induction {m} z s)

data Pos :: Num -> * where
  Pos :: forall (m :: Num). 0 <= m => Pos m

data MulPos :: Num -> Num -> * where
  MulPos :: forall (m n :: Num) . 0 <= m * n => MulPos m n

mulPos :: pi (m n :: Nat) . MulPos m n
mulPos {m} {n} = 
  let
    step :: forall (x :: Nat) . MulPos m x -> MulPos m (x + 1)
    step MulPos = MulPos
  in induction {n} MulPos step

elimMulPos :: forall a (m n :: Num) . MulPos m n -> (0 <= m * n => a) -> a
elimMulPos MulPos x = x

lemmaMulPos :: forall a. pi (m n :: Nat) . (0 <= m * n => a) -> a
lemmaMulPos {m} {n} = elimMulPos (mulPos {m} {n})



data Prf :: * -> * where
  Prf :: forall a. Prf a

prf :: forall a . a -> Prf a
prf _ = Prf

ind :: forall (f :: Num -> *)(m :: Nat) . Prf (f 0) ->
           (forall (n :: Nat) . Prf (f n) -> Prf (f (n+1))) ->
               Prf (f m)
ind _ _ = Prf


data Proxy :: Num -> * where
  Proxy :: forall (n :: Num) . Proxy n

data ProxyNN :: (Num -> Num) -> * where
  ProxyNN :: forall (f :: Num -> Num) . ProxyNN f

indy :: forall (f :: Nat -> Nat)(m :: Nat) b . 0 <= f 0 => ProxyNN f ->
          (forall (x :: Num) a . Proxy x -> (0 <= x => a) -> a) ->
            (forall (n :: Nat) a . 0 <= f n => (0 <= f (n+1) => a) -> a) ->
              (0 <= f m => b) -> b
indy _ lie s e = lie (Proxy :: Proxy (f m)) e

{-
possy :: forall a (m n :: Nat) .
                     (forall (x :: Num) a . Proxy x -> (0 <= x => a) -> a) ->
                         (0 <= m * n => a) -> a
possy lie =
    let foo :: forall (n :: Nat) a . 0 <= m * n => (0 <= m * (n + 1) => a) -> a
        foo x = x
    in indy (ProxyNN :: ProxyNN ((*) m)) lie foo
-}



foo :: forall (f :: Num -> Num -> Num) a .
           (forall (m n :: Num) a . Proxy m -> Proxy n -> (f m n ~ f n m => a) -> a) ->
               (f 1 3 ~ f 3 1 => a) -> a
foo comm x = comm (Proxy :: Proxy 1) (Proxy :: Proxy 3) x