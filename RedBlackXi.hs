{-# OPTIONS_GHC -F -pgmF ./toy #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables #-}

{-# This is closely based on the red-black tree example in Xi's thesis. #-}

module RedBlack where

data Entry :: * -> * where
  X :: forall a . Integer -> a -> Entry a

-- Dict a cl bh rh s is an RBT with
--   a = element type
--   cl = colour (0 = black, 1 = red)
--   bh = black height (must be same for both subtrees)
--   rh = red height (must be 0 for balance)
--   s  = size
-- if the root is black, the tree is balanced

data Dict :: * -> Num -> Num -> Num -> Num -> * where
  Empty :: forall a . Dict a 0 0 0 0
  Black :: forall a (cl cr bh sl sr :: Nat) .
               Entry a ->
                   Dict a cl bh 0 sl ->
                       Dict a cr bh 0 sr ->
                           Dict a 0 (bh+1) 0 (sl+sr+1)
  Red :: forall a (cl cr bh rhl rhr sl sr :: Nat) .
               Entry a ->
                   Dict a cl bh rhl sl ->
                       Dict a cr bh rhr sr ->
                           Dict a 1 bh (cl+cr+rhl+rhr) (sl+sr+1)


lookup dict key =
  let
      lk' (X key1 datum1) left right = 
        let
            f EQ  = Just datum1
            f LT  = lk left
            f GT  = lk right
        in f (compare key key1)
       
      lk :: forall a (cl bh rh s :: Num) . Dict a cl bh rh s -> Maybe a
      lk Empty          = Nothing
      lk (Red e l r)    = lk' e l r
      lk (Black e l r)  = lk' e l r
  
  in lk dict


{-
insert :: forall a p (c bh s :: Num) . Dict a c bh 0 s -> Entry a ->
              p ->
              (forall (nc bhx :: Nat) . nc <= 1, bhx <= 1 => Dict a nc (bh+bhx) 0 (s+1) -> p) ->
                  p
insert dict (X key datum) found added =
  let
      ins :: forall (c bh s :: Num) . Dict a c bh 0 s ->
                 (forall (nc :: Nat) . nc <= 1 => Dict a nc bh 0 (s+1) -> p) ->
                 (forall (nrh :: Nat). nrh <= 1 => Dict a 1 bh nrh (s+1) -> p) ->
                 p
      ins = ins

      fix1 :: forall (nc :: Nat) . nc <= 1 => Dict a nc bh 0 (s+1) -> p
      fix1 (Black e l r) = added (Black e l r)
      fix1 (Red e (Red el ll lr) r)  = added (Black e (Red el ll lr) r)
      fix1 (Red e l (Red er rl rr))  = added (Black e l (Red er rl rr))
      fix1 (Red e (Black el ll lr) (Black er rl rr)) =
          added (Red e (Black el ll lr) (Black er rl rr))
      fix1 (Red e Empty Empty) = added (Red e Empty Empty)


      fix2 :: forall (nrh :: Nat). nrh <= 1 => Dict a 1 bh nrh (s+1) -> p
      fix2 (Red e (Red el ll lr) r)  = added (Black e (Red el ll lr) r)
      fix2 (Red e l (Red er rl rr))  = added (Black e l (Red er rl rr))
      fix2 (Red e (Black el ll lr) (Black er rl rr)) =
          added (Red e (Black el ll lr) (Black er rl rr))
      fix2 (Red e Empty Empty) = added (Red e Empty Empty)
  in ins dict fix1 fix2
-}



data Tree :: * -> Num -> Num -> Num -> * where
  E   :: forall a . Tree a 0 0 0
  TR  :: forall a (bh cl cr :: Nat) .
             Tree a cl bh 0 -> a -> Tree a cr bh 0 -> Tree a 1 bh (cl+cr)
  TB  :: forall a (cl cr bh :: Nat) .
             Tree a cl bh 0 -> a -> Tree a cr bh 0 -> Tree a 0 (bh+1) 0

member :: forall a (cl bh rd :: Num) .
              (a -> a -> Ordering) -> a -> Tree a cl bh rd -> Bool
member cmp x E = False
member cmp x (TR a y b) = 
  let
    case_ LT = member cmp x a
    case_ EQ = True
    case_ GT = member cmp x b
  in case_ (cmp x y)
member cmp x (TB a y b) = 
  let
    case_ LT = member cmp x a
    case_ EQ = True
    case_ GT = member cmp x b
  in case_ (cmp x y)

-- insert :: forall a . (a -> a -> Ordering) -> a -> Tree a -> Tree a
insert cmp x s =
  let
      balanceB :: forall a p (cl cr bh rl rr :: Nat) . rl+rr <= 1 =>
                    Tree a cl bh rl -> a -> Tree a cr bh rr ->
                      (forall (c x :: Nat) . x <= 1 => Tree a c (bh+x) 0 -> p) -> p
      balanceB (TR (TR a x b) y c) z d  q = q (TR (TB a x b) y (TB c z d))
      balanceB (TR a x (TR b y c)) z d  q = q (TR (TB a x b) y (TB c z d))
      balanceB a x (TR (TR b y c) z d)  q = q (TR (TB a x b) y (TB c z d))
      balanceB a x (TR b y (TR c z d))  q = q (TR (TB a x b) y (TB c z d))
      balanceB (TB a x b) y (TB c z d)  q = q (TB (TB a x b) y (TB c z d))
      -- more identical cases

      balanceR :: forall a (cl bh rl rr :: Nat) . rl+rr <= 1 => 
                  Tree a cl bh rl -> a -> Tree a cl bh rr -> Tree a cl (bh+1) 0
      balanceR (TR (TR a x b) y c) z d  = TR (TB a x b) y (TB c z d)
      balanceR (TR a x (TR b y c)) z d  = TR (TB a x b) y (TB c z d)
      balanceR a x (TR (TR b y c) z d)  = TR (TB a x b) y (TB c z d)
      balanceR a x (TR b y (TR c z d))  = TR (TB a x b) y (TB c z d)
      --- balanceR a x b                    = TR a x b

      ins :: forall a p (cl bh :: Num) . Tree a cl bh 0 ->
                 (forall (c rd :: Nat) . rd <= 1 => Tree a c bh rd -> p) -> p
      ins E           q = q (TR E x E)
      ins (TR a y b)  q =
        let
            f :: forall (c rd :: Nat) . rd <= 1 => Tree a c bh rd -> p
            f a' = balanceB a' y b q

            case_ LT  = ins a f
            case_ EQ  = TR a y b
            case_ GT  = ins b (\ b' -> q (balanceR a y b'))
        in case_ (cmp x y)
      ins (TB a y b) q =
        let
            case_ LT  = balanceB (ins a) y b
            case_ EQ  = TB a y b
            case_ GT  = balanceB a y (ins b)
        in case_ (cmp x y)

      makeBlack :: forall a (cl bh :: Num) . Tree a cl bh 0 -> Tree a 0 bh 0
      makeBlack (TR a y b) = TB a y b
      makeBlack (TB a y b) = TB a y b
  in ins s makeBlack
  