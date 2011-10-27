{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Delay where

data D :: Num -> * -> * where
  D :: forall a (n :: Num) . a -> D n a
  deriving Show

pure = D

ap :: forall a b (n :: Num) . D n (a -> b) -> D n a -> D n b
ap (D f) (D s) = D (f s)

delay :: forall a (n k :: Num) . 0 <= k => D n a -> D (n+k) a
delay (D x) = D x

splat :: forall a . pi (k :: Nat) . (forall (n :: Nat) . D (n+k) a) -> a
splat {k} dx = let unD :: D (k+1) a -> a
                   unD (D x) = x
               in unD dx


fix :: forall a (n :: Nat) . (D n a -> a) -> a
fix f = f (pure (fix f))



data Tree :: * -> * where
  Leaf :: forall a . a -> Tree a
  Node :: forall a . Tree a -> Tree a -> Tree a
  deriving Show

repMin :: forall a. (a -> a -> a) -> Tree a -> Tree a
repMin min_ t =
  let help :: Tree a -> a -> (Tree a, a)
      help (Leaf x) y = (Leaf y, x)
      help (Node l r) y =
        let lm = help l y
            rm = help r y
        in (Node (fst lm) (fst rm), min_ (snd lm) (snd rm))
          
      ans = help t (snd ans)
  in fst ans


repMin2 :: forall a. (a -> a -> a) -> Tree a -> D 1 (Tree a)
repMin2 min_ t =
  let help :: Tree a -> D 1 a -> (D 1 (Tree a), a)
      help (Leaf x) dy = (ap (pure Leaf) dy, x)
      help (Node l r) dy =
        let lm = help l dy
            rm = help r dy
        in (ap (ap (pure Node) (fst lm)) (fst rm), min_ (snd lm) (snd rm))
          
      ans = fix (\ x -> help t (ap (pure snd) x))
  in fst ans

repMin3 :: forall a (n :: Nat). (a -> a -> a) -> Tree a -> D (n+1) (Tree a)
repMin3 min_ t =
  let help :: Tree a -> D (n+1) a -> (D (n+1) (Tree a), a)
      help (Leaf x) dy = (ap (pure Leaf) dy, x)
      help (Node l r) dy =
        let lm = help l dy
            rm = help r dy
        in (ap (ap (pure Node) (fst lm)) (fst rm), min_ (snd lm) (snd rm))
          
      ans = fix (\ x -> help t (ap (pure snd) x))
  in fst ans

repMin4 min_ t = splat {1} (repMin3 min_ t)
            