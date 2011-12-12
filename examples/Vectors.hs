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

vapp = vzipWith ($)

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
plan {0}           = VNil
plan {m} | {m > 0} = VCons m (plan {m-1})

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


type Matrix a (m :: Nat) (n :: Nat) = Vec (Vec a n) m

mid :: forall a . Num a => pi (n :: Nat) . Matrix a n n
mid {0}   = VNil
mid {n+1} = VCons (VCons 1 (vec {n} 0))
                  (vmap (VCons 0) (mid {n}))

mfill :: pi (m n :: Nat) . a -> Matrix a m n
mfill {m} {n} x = vec {m} (vec {n} x)

mmult :: forall a (i j k :: Nat) . Num a => Matrix a i j -> Matrix a j k -> Matrix a i k
mmult xij yjk = vmap (\ xj -> colSum (vzipWith ((.) vmap (*)) xj yjk)) xij
  where
    colSum :: forall a (m n :: Nat) . Num a => Vec (Vec a n) m -> Vec a n
    colSum (VCons xs VNil) = xs
    colSum (VCons xs xss) = vzipWith (+) xs (colSum xss)

mshow :: forall a (m n :: Nat) . Show a => Matrix a m n -> String
mshow VNil = ""
mshow (VCons xs xss) = (++) (vshow xs) ('\n' : mshow xss) 
  where
    vshow :: forall (i :: Nat) . Vec a i -> String
    vshow VNil = ""
    vshow (VCons y ys) = (++) (show y) ('\t' : vshow ys) 

m1234 :: Matrix Integer 2 2
m1234 = VCons (VCons 1 (VCons 2 VNil))
          (VCons (VCons 3 (VCons 4 VNil)) VNil) 
