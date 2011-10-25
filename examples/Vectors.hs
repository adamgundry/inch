{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Vectors where

data Vec :: * -> Nat -> * where
  VNil  :: Vec a 0
  VCons :: forall a (n :: Nat) . a -> Vec a n -> Vec a (n+1)
  deriving Show

vhead :: forall (n :: Nat) a. Vec a (n+1) -> a
vhead (VCons x _) = x

vtail :: forall (n :: Nat) a. Vec a (n+1) -> Vec a n
vtail (VCons _ xs) = xs

vappend :: forall (m n :: Nat) a .
                Vec a m -> Vec a n -> Vec a (m+n)
vappend VNil         ys = ys
vappend (VCons x xs) ys = VCons x (vappend xs ys)

vreverse :: forall (n :: Nat) a . Vec a n -> Vec a n
vreverse xs = vrevapp xs VNil
  where
    vrevapp :: forall (m n :: Nat) a . Vec a m -> Vec a n -> Vec a (m+n)
    vrevapp VNil         ys = ys
    vrevapp (VCons x xs) ys = vrevapp xs (VCons x ys)

vec :: pi (n :: Nat) . a -> Vec a n
vec {0}   a = VNil
vec {n+1} a = VCons a (vec {n} a)

vmap :: forall (n :: Nat) a b . (a -> b) -> Vec a n -> Vec b n
vmap f VNil         = VNil
vmap f (VCons x xs) = VCons (f x) (vmap f xs)

vzipWith :: forall (n :: Nat) a b c .
                (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
vzipWith f VNil VNil = VNil
vzipWith f (VCons x xs) (VCons y ys) = VCons (f x y) (vzipWith f xs ys)

vzip = vzipWith (,)

vifold :: forall (n :: Nat) a (f :: Nat -> *) .
           f 0 -> (forall (m :: Nat) . a -> f m -> f (m + 1)) ->
             Vec a n -> f n
vifold n c VNil         = n
vifold n c (VCons x xs) = c x (vifold n c xs)

vid = vifold VNil VCons


data K :: * -> Integer -> * where
  K :: forall a (n :: Integer) . a -> K a n
  deriving Show

unK (K a) = a

vfold :: forall (n :: Nat) a b . b -> (a -> b -> b) -> Vec a n -> b
vfold n c xs = unK (vifold (K n) (\ x ky -> K (c x (unK ky))) xs)

vsum      = vfold 0 (+)
vec2list  = vfold [] (:)


plan :: pi (n :: Nat) . Vec Integer n
plan {0}   = VNil
plan {m+1} = VCons m (plan {m})

vlookup :: forall (n :: Nat) a . pi (m :: Nat) . m < n => Vec a n -> a
vlookup {0}   (VCons x _)  = x
vlookup {k+1} (VCons _ xs) = vlookup {k} xs

vsplit :: forall (n :: Nat) a . pi (m :: Nat) . Vec a (m + n) -> (Vec a m, Vec a n)
vsplit {0}   xs           = (VNil, xs)
vsplit {m+1} (VCons x xs) = case vsplit {m} xs of
                                (ys, zs) -> (VCons x ys, zs)

vjoin :: forall a (m :: Nat) . Vec (Vec a m) m -> Vec a m
vjoin VNil                     = VNil
vjoin (VCons (VCons x xs) xss) = VCons x (vjoin (vmap vtail xss))

vsnoc :: forall a (n :: Nat) . Vec a n -> a -> Vec a (n+1)
vsnoc VNil          a = VCons a VNil
vsnoc (VCons x xs)  a = VCons x (vsnoc xs a)