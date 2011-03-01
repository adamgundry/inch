{-# OPTIONS_GHC -F -pgmF ./toy #-}
{-# LANGUAGE ExplicitForAll, GADTs, KindSignatures #-}

-- Combinators

k        = \ x y -> x
s x y z  = x z (y z)
i        = s k k 
app f s  = f s
comp f g = \ x -> f (g x)

-- Data types

data Bools where
  TT :: Bools
  FF :: Bools

data Nat where
  Zero :: Nat
  Suc :: Nat -> Nat

data List :: * -> * where
  Nil :: forall a. List a
  Cons :: forall a. a -> List a -> List a

{-
data Vec :: Num -> * -> * where
  VNil :: forall a. Vec 0 a
  VCons :: forall (n :: Num) a . 0 <= n => a -> Vec n a -> Vec (n+1) a
-}

data Vec :: Num -> * -> * where
  VNil :: forall (n :: Num) a . n ~ 0 => Vec n a
  VCons :: forall (n m :: Num) a . 0 <= n, m ~ (n + 1) => a -> Vec n a -> Vec m a

data UNat :: Num -> * where
  UZero :: forall (n :: Num) . n ~ 0 => UNat n
  USuc :: forall (n m :: Num). 0 <= n, m ~ (n + 1) => UNat n -> UNat m


-- Vector kit

vhead :: forall (n :: Num) a. 0 <= n => Vec (n+1) a -> a
vhead (VCons x xs) = x

vtail :: forall (n :: Num) a. 0 <= n => Vec (n+1) a -> Vec n a
vtail (VCons x xs) = xs

vtail2 :: forall (n :: Num) a. 0 <= n => Vec (n+2) a -> Vec n a
vtail2 (VCons x (VCons y xs)) = xs

vtail3 :: forall (n :: Num) a. 1 <= n => Vec n a -> Vec (n-1) a
vtail3 (VCons x xs) = xs

vtail4 :: forall (n :: Num) a. 1 <= n => Vec n a -> Vec (n-1) a
vtail4 (VCons x xs) = xs

twotails :: forall (n :: Num) a. 0 <= n => Vec (n+2) a -> Vec n a
twotails xs = vtail (vtail xs)

-- thing :: forall a (n m :: Num) . 1 <= n, n <= m => Vec n (Vec m a) -> Vec (m-1) a
thing = comp vtail vhead


vappend :: forall (m n :: Num) a . 0 <= n => Vec m a -> Vec n a -> Vec (m+n) a
vappend VNil ys = ys
vappend (VCons x xs) ys = VCons x (vappend xs ys)

vrevapp :: forall (m n :: Num) a . 0 <= n => Vec m a -> Vec n a -> Vec (m+n) a
vrevapp VNil ys = ys
vrevapp (VCons x xs) ys = vrevapp xs (VCons x ys)

vec :: forall (n :: Num) a. UNat n -> a -> Vec n a
vec UZero    a = VNil
vec (USuc m) a = VCons a (vec m a)


vid :: forall (n :: Num) a . Vec n a -> Vec n a
vid VNil          = VNil
vid (VCons x xs)  = VCons x (vid xs)


bottom :: forall a. a
bottom = bottom

unaryToNat :: forall (n :: Num) . UNat n -> Nat
unaryToNat UZero    = Zero
unaryToNat (USuc m) = Suc (unaryToNat m)

plan :: forall (n :: Num) . UNat n -> Vec n Nat
plan UZero = VNil
plan (USuc m) = VCons (unaryToNat m) (plan m)


vlookup :: forall (n m :: Num) a . 0 <= m, (m+1) <= n => Vec n a -> UNat m -> a
vlookup (VCons x xs) UZero = x
vlookup (VCons x xs) (USuc m) = vlookup xs m


one      = Suc Zero
two      = Suc one
three    = Suc two
v123     = VCons one (VCons two (VCons three VNil))
right    = vhead v123
righter  = app vtail v123
