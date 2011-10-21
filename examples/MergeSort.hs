{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module MergeSort where

comp f g = \ x -> f (g x)

data Vec :: Num -> * -> * where
  Nil :: forall a. Vec 0 a
  Cons :: forall (n :: Num) a . 0 <= n => a -> Vec n a -> Vec (n+1) a

data DTree :: * -> Num -> * where
  Empty  :: forall a. DTree a 0
  Leaf   :: forall a. a -> DTree a 1
  Even   :: forall a (n :: Num) . 1 <= n =>
               DTree a n -> DTree a n -> DTree a (2*n)
  Odd    :: forall a (n :: Num) . 1 <= n =>
               DTree a (n+1) -> DTree a n -> DTree a (2*n+1)

insert :: forall a (n :: Num) . a -> DTree a n -> DTree a (n+1)
insert i Empty       = Leaf i
insert i (Leaf j)    = Even (Leaf i) (Leaf j)
insert i (Even l r)  = Odd (insert i l) r
insert i (Odd l r)   = Even l (insert i r)


lt :: Bool -> Bool -> Bool
lt True  _  = False
lt False b  = b

merge :: forall (m n :: Num) .
             Vec m Bool -> Vec n Bool -> Vec (m+n) Bool
merge Nil ys = ys
merge xs Nil = xs
merge (Cons x xs) (Cons y ys) | lt x y = Cons x (merge xs (Cons y ys))
merge (Cons x xs) (Cons y ys) | True   = Cons y (merge (Cons x xs) ys)


vfold :: forall (n :: Num) a (f :: Num -> *) . f 0 ->
    (forall (m :: Num) . 0 <= m => a -> f m -> f (m + 1)) -> Vec n a -> f n
vfold n c Nil         = n
vfold n c (Cons x xs) = c x (vfold n c xs)


build = vfold Empty insert

flatten :: forall (n :: Num) . DTree Bool n -> Vec n Bool
flatten Empty      = Nil
flatten (Leaf i)   = Cons i Nil
flatten (Even l r) = merge (flatten l) (flatten r)
flatten (Odd l r)  = merge (flatten l) (flatten r)

sort = comp flatten build


data OVec :: Num -> Num -> Num -> * where
  ONil :: forall (l u :: Num) . l <= u => OVec 0 l u
  OCons :: forall (n l u :: Num) . pi (x :: Num) . l <= x =>
               OVec n x u -> OVec (n+1) l u


ltCompare :: forall a. pi (x y :: Num) . (x <= y => a) -> (x > y => a) -> a
ltCompare {x} {y} l g | {x <= y} = l
ltCompare {x} {y} l g | {x  > y} = g

omerge :: forall (m n l u :: Num) . OVec m l u -> OVec n l u -> OVec (m+n) l u
omerge ONil ys = ys
omerge xs ONil = xs
omerge (OCons {x} xs) (OCons {y} ys)
    = ltCompare {x} {y} (OCons {x} (omerge xs (OCons {y} ys)))
                        (OCons {y} (omerge (OCons {x} xs) ys))



data In :: Num -> Num -> * where
  In :: forall (l u :: Num) . pi (x :: Num) . l <= x, x <= u => In l u

oflatten :: forall (n l u :: Num) . l <= u => DTree (In l u) n -> OVec n l u
oflatten Empty      = ONil
oflatten (Leaf (In {i}))   = OCons {i} ONil
oflatten (Even l r) = omerge (oflatten l) (oflatten r)
oflatten (Odd l r)  = omerge (oflatten l) (oflatten r)

osort = comp oflatten build