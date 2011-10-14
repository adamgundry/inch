{-# OPTIONS_GHC -F -pgmF ./toy #-}
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