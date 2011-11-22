{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module MergeSort where

import Vectors

comp f g x = f (g x)

data DTree :: * -> Integer -> * where
    Empty  :: DTree a 0
    Leaf   :: a -> DTree a 1
    Even   :: forall a (n :: Integer) . 1 <= n =>
                 DTree a n -> DTree a n -> DTree a (2*n)
    Odd    :: forall a (n :: Integer) . 1 <= n =>
                 DTree a (n+1) -> DTree a n -> DTree a (2*n+1)
  deriving Show

insert :: forall a (n :: Integer) . a -> DTree a n -> DTree a (n+1)
insert i Empty       = Leaf i
insert i (Leaf j)    = Even (Leaf i) (Leaf j)
insert i (Even l r)  = Odd (insert i l) r
insert i (Odd l r)   = Even l (insert i r)

merge :: forall (m n :: Integer) .
             Vec Integer m -> Vec Integer n -> Vec Integer (m+n)
merge VNil ys = ys
merge xs VNil = xs
merge (VCons x xs) (VCons y ys) | (<=) x y   = VCons x (merge xs (VCons y ys))
                                | otherwise  = VCons y (merge (VCons x xs) ys)

build = vifold Empty insert

flatten :: forall (n :: Integer) . DTree Integer n -> Vec Integer n
flatten Empty      = VNil
flatten (Leaf i)   = VCons i VNil
flatten (Even l r) = merge (flatten l) (flatten r)
flatten (Odd l r)  = merge (flatten l) (flatten r)

sort = comp flatten build


data OVec :: Integer -> Integer -> Integer -> * where
  ONil :: forall (l u :: Integer) . l <= u => OVec 0 l u
  OCons :: forall (n l u :: Integer) . pi (x :: Integer) . l <= x =>
               OVec n x u -> OVec (n+1) l u
  deriving Show


ltCompare :: forall a. pi (x y :: Integer) . (x <= y => a) -> (x > y => a) -> a
ltCompare {x} {y} l g | {x <= y} = l
ltCompare {x} {y} l g | {x  > y} = g

omerge :: forall (m n l u :: Integer) . OVec m l u -> OVec n l u -> OVec (m+n) l u
omerge ONil ys = ys
omerge xs ONil = xs
omerge (OCons {x} xs) (OCons {y} ys)
    = ltCompare {x} {y} (OCons {x} (omerge xs (OCons {y} ys)))
                        (OCons {y} (omerge (OCons {x} xs) ys))


data In :: Integer -> Integer -> * where
    In :: forall (l u :: Integer) . pi (x :: Integer) . (l <= x, x <= u) => In l u
  deriving Show

oflatten :: forall (n l u :: Integer) . l <= u => DTree (In l u) n -> OVec n l u
oflatten Empty      = ONil
oflatten (Leaf (In {i}))   = OCons {i} ONil
oflatten (Even l r) = omerge (oflatten l) (oflatten r)
oflatten (Odd l r)  = omerge (oflatten l) (oflatten r)

osort = comp oflatten build