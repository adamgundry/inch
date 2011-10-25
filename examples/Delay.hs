{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Delay where

data Pair :: * -> * -> * where
  Pair :: forall a b. a -> b -> Pair a b

p1 (Pair a _) = a
p2 (Pair _ b) = b




data D :: Num -> * -> * where
  D :: forall a (n :: Num) . a -> D n a

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


repMin :: forall a. (a -> a -> a) -> Tree a -> Tree a
repMin min_ t =
  let help :: Tree a -> a -> Pair (Tree a) a
      help (Leaf x) y = Pair (Leaf y) x
      help (Node l r) y =
        let lm = help l y
            rm = help r y
        in Pair (Node (p1 lm) (p1 rm)) (min_ (p2 lm) (p2 rm))
          
      ans = help t (p2 ans)
  in p1 ans


repMin2 :: forall a. (a -> a -> a) -> Tree a -> D 1 (Tree a)
repMin2 min_ t =
  let help :: Tree a -> D 1 a -> Pair (D 1 (Tree a)) a
      help (Leaf x) dy = Pair (ap (pure Leaf) dy) x
      help (Node l r) dy =
        let lm = help l dy
            rm = help r dy
        in Pair (ap (ap (pure Node) (p1 lm)) (p1 rm)) (min_ (p2 lm) (p2 rm))
          
      ans = fix (\ x -> help t (ap (pure p2) x))
  in p1 ans

repMin3 :: forall a (n :: Nat). (a -> a -> a) -> Tree a -> D (n+1) (Tree a)
repMin3 min_ t =
  let help :: Tree a -> D (n+1) a -> Pair (D (n+1) (Tree a)) a
      help (Leaf x) dy = Pair (ap (pure Leaf) dy) x
      help (Node l r) dy =
        let lm = help l dy
            rm = help r dy
        in Pair (ap (ap (pure Node) (p1 lm)) (p1 rm)) (min_ (p2 lm) (p2 rm))
          
      ans = fix (\ x -> help t (ap (pure p2) x))
  in p1 ans

repMin4 min_ t = splat {1} (repMin3 min_ t)
            