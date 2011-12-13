{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module State where

data State :: (Integer -> *) -> Integer -> * where
    Return :: forall (x :: Integer -> *)(i :: Integer) . x i -> State x i
    Get    :: forall (x :: Integer -> *)(i :: Integer) .
                  (pi (j :: Integer) . i ~ j => State x i) -> State x i
    Put    :: forall (x :: Integer -> *)(i :: Integer) .
                  pi (j :: Integer) . State x j -> State x i

data Sig :: (Integer -> *) -> * where
    Con :: forall (x :: Integer -> *) . pi (i :: Integer) . x i -> Sig x
  deriving Show

runState :: forall (x :: Integer -> *) . pi (i :: Integer) . State x i -> Sig x
runState {i} (Return a)   = Con {i} a
runState {i} (Get f)      = runState {i} (f {i})
runState {i} (Put {j} s)  = runState {j} s