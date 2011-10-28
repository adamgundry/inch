{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

{-
  A library for time complexity analysis, based on

    Nils Anders Danielsson. 2008. Lightweight semiformal time
    complexity analysis for purely functional data structures.

    In Proceedings of the 35th annual ACM SIGPLAN-SIGACT symposium on
    Principles of Programming Languages (POPL '08). ACM.
-}

module Cost (Cost, weaken, force, returnCost, bindCost, weakenBy,
                 tick, returnW, joinCost, mapCost) where

-- Cost is a monad indexed by the number of time steps required to
-- deliver a value in WHNF. 

-- Note that the Hide constructor is not exported, so clients cannot
-- violate the abstraction barrier, though they must still annotate
-- code appropriately (not misusing force, for example).

data Cost :: Num -> * -> * where
  Hide :: forall (n :: Nat) a . a -> Cost n a

weaken :: forall (m n :: Nat) a . m <= n => Cost m a -> Cost n a
weaken (Hide a) = Hide a

force :: forall (n :: Nat) a . Cost n a -> a
force (Hide a) = a

returnCost :: a -> Cost 0 a
returnCost = Hide

bindCost :: forall (m n :: Nat) a b . Cost m a ->
                (a -> Cost n b) -> Cost (m+n) b
bindCost x f = weaken (f (force x))


-- Given the above primitives, we define some useful derived combinators:

weakenBy :: forall (n :: Nat) a . pi (m :: Nat) . Cost n a -> Cost (m + n) a
weakenBy {m} = weaken

tick :: forall (n :: Nat) a . Cost n a -> Cost (n + 1) a
tick = weakenBy {1}

returnW :: forall (n :: Nat) a . a -> Cost n a
returnW x = weaken (returnCost x)

joinCost :: forall (m n :: Nat) a . Cost m (Cost n a) -> Cost (m + n) a
joinCost x = bindCost x id

mapCost :: forall (n :: Nat) a b . (a -> b) -> Cost n a -> Cost n b
mapCost f x = bindCost x (\ x -> returnW (f x))