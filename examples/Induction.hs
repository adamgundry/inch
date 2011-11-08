{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Induction where

induction :: forall (f :: Integer -> *) . pi (m :: Nat) . f 0 -> (forall (n :: Nat) . f n -> f (n+1)) -> f m
induction {0} z s = z
induction {m+1} z s = s (induction {m} z s)

data Pos :: Integer -> * where
  Pos :: forall (m :: Integer). 0 <= m => Pos m

data MulPos :: Integer -> Integer -> * where
  MulPos :: forall (m n :: Integer) . 0 <= m * n => MulPos m n

mulPos :: pi (m n :: Nat) . MulPos m n
mulPos {m} {n} = 
  let
    step :: forall (x :: Nat) . MulPos m x -> MulPos m (x + 1)
    step MulPos = MulPos
  in induction {n} MulPos step

elimMulPos :: forall a (m n :: Integer) . MulPos m n -> (0 <= m * n => a) -> a
elimMulPos MulPos x = x

lemmaMulPos :: forall a. pi (m n :: Nat) . (0 <= m * n => a) -> a
lemmaMulPos {m} {n} = elimMulPos (mulPos {m} {n})



data Prf :: * -> * where
  Prf :: forall a. Prf a

prf :: forall a . a -> Prf a
prf _ = Prf

ind :: forall (f :: Integer -> *)(m :: Nat) . Prf (f 0) ->
           (forall (n :: Nat) . Prf (f n) -> Prf (f (n+1))) ->
               Prf (f m)
ind _ _ = Prf


data Proxy :: Integer -> * where
  Proxy :: forall (n :: Integer) . Proxy n

data ProxyNN :: (Integer -> Integer) -> * where
  ProxyNN :: forall (f :: Integer -> Integer) . ProxyNN f

indy :: forall (f :: Nat -> Nat)(m :: Nat) b . 0 <= f 0 => ProxyNN f ->
          (forall (x :: Integer) a . Proxy x -> (0 <= x => a) -> a) ->
            (forall (n :: Nat) a . 0 <= f n => (0 <= f (n+1) => a) -> a) ->
              (0 <= f m => b) -> b
indy _ lie s e = lie (Proxy :: Proxy (f m)) e

{-
possy :: forall a (m n :: Nat) .
                     (forall (x :: Integer) a . Proxy x -> (0 <= x => a) -> a) ->
                         (0 <= m * n => a) -> a
possy lie =
    let foo :: forall (n :: Nat) a . 0 <= m * n => (0 <= m * (n + 1) => a) -> a
        foo x = x
    in indy (ProxyNN :: ProxyNN ((*) m)) lie foo
-}



foo :: forall (f :: Integer -> Integer -> Integer) a .
           (forall (m n :: Integer) a . Proxy m -> Proxy n -> (f m n ~ f n m => a) -> a) ->
               (f 1 3 ~ f 3 1 => a) -> a
foo comm x = comm (Proxy :: Proxy 1) (Proxy :: Proxy 3) x



data Dict :: Constraint -> * where
  Dict :: forall (c :: Constraint) . c => Dict c

data ProxyNC :: (Integer -> Constraint) -> * where
  ProxyNC :: forall (p :: Integer -> Constraint) . ProxyNC p

indict :: forall (p :: Integer -> Constraint) (m :: Nat) .
              ProxyNC p -> 
              Dict (p 0) ->
                (forall (n :: Nat) . Dict (p n) -> Dict (p (n + 1))) ->
                  Dict (p m) 
indict = indict


lemmaMulPos2 :: forall (m n :: Nat) . Dict (0 <= n)
lemmaMulPos2 = indict (ProxyNC :: ProxyNC ((<=) 0)) Dict step
  where
    step :: forall (x :: Nat) . Dict (0 <= x) -> Dict (0 <= x + 1)
    step = undefined



indc :: forall (p :: Nat -> Constraint)(m :: Nat) b . p 0 =>
          ProxyNC p ->
          Proxy m ->
            (forall (n :: Nat) a . p n => Proxy n -> (p (n+1) => a) -> a) ->
              (p m => b) -> b
indc = indc


data Comp :: (Nat -> Constraint) -> (Nat -> Nat) -> Nat -> * where
  Comp :: forall (g :: Nat -> Constraint) (f :: Nat -> Nat) (n :: Nat) . 
              Dict (g (f n)) -> Comp g f n 

{-
lemmaMulPos3 :: forall a (m n :: Nat) . ((Comp ((<=) 0) ((*) m) n) -> a) -> a
lemmaMulPos3 = indc (undefined :: ProxyNC (Comp ((<=) 0) ((*) m))) undefined undefined
-}

{-
data Comp' :: (k2 -> *) -> (k1 -> k2) -> k1 -> * where
  Comp' :: forall (g :: k2 -> *) (f :: k1 -> k2) (x :: k1) . g (f x) -> Comp' g f x
-}