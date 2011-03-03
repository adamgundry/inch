{-# OPTIONS_GHC -F -pgmF ./toy #-}
{-# LANGUAGE ExplicitForAll, GADTs, KindSignatures #-}

module Example where

-- Combinators

k        = \ x y -> x
s x y z  = x z (y z)
i        = s k k 
app f s  = f s
comp f g = \ x -> f (g x)
fix f    = f (fix f)

-- Data types

data Bools where
  TT :: Bools
  FF :: Bools

data Pair :: * -> * -> * where
  Pair :: forall a b. a -> b -> Pair a b

data Nat where
  Zero :: Nat
  Suc :: Nat -> Nat

{-
data Vec :: Num -> * -> * where
  VNil :: forall a. Vec 0 a
  VCons :: forall (n :: Num) a . 0 <= n => a -> Vec n a -> Vec (n+1) a
-}

data Vec :: Num -> * -> * where
  VNil :: forall (n :: Num) a . n ~ 0 => Vec n a
  VCons :: forall (n m :: Num) a . 1 <= n => a -> Vec (n-1) a -> Vec n a

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

vreverse :: forall (n :: Num) a . Vec n a -> Vec n a
vreverse xs = vrevapp xs VNil

vec :: forall (n :: Num) a. UNat n -> a -> Vec n a
vec UZero    a = VNil
vec (USuc m) a = VCons a (vec m a)

vid :: forall (n :: Num) a . Vec n a -> Vec n a
vid VNil          = VNil
vid (VCons x xs)  = VCons x (vid xs)

vmap :: forall (n :: Num) a b . (a -> b) -> Vec n a -> Vec n b
vmap f VNil = VNil
vmap f (VCons x xs) = VCons (f x) (vmap f xs)

vzipWith :: forall (n :: Num) a b c . (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
vzipWith f VNil VNil = VNil
vzipWith f (VCons x xs) (VCons y ys) = VCons (f x y) (vzipWith f xs ys)



unaryToNat :: forall (n :: Num) . UNat n -> Nat
unaryToNat UZero    = Zero
unaryToNat (USuc m) = Suc (unaryToNat m)

plan :: forall (n :: Num) . UNat n -> Vec n Nat
plan UZero = VNil
plan (USuc m) = VCons (unaryToNat m) (plan m)


vlookup :: forall (n m :: Num) a . 0 <= m, (m+1) <= n => Vec n a -> UNat m -> a
vlookup (VCons x xs) UZero = x
vlookup (VCons x xs) (USuc m) = vlookup xs m


pairMap :: forall a b c d . (a -> c) -> (b -> d) -> Pair a b -> Pair c d
pairMap f g (Pair a b) = Pair (f a) (g b)

{-
vsplit :: forall (m n :: Num) a . UNat m -> Vec (m + n) a -> Pair (Vec m a) (Vec n a)
vsplit UZero xs = Pair VNil xs
vsplit (USuc i) (VCons x xs) = pairMap (VCons x) i (vsplit i xs)
-}

vtake :: forall (m n :: Num) a . UNat m -> Vec (m + n) a -> Vec m a
vtake UZero    xs           = VNil
vtake (USuc i) (VCons x xs) = VCons x (vtake i xs)


one      = Suc Zero
two      = Suc one
three    = Suc two
v123     = VCons one (VCons two (VCons three VNil))
right    = vhead v123
righter  = app vtail v123


bottom :: forall a. a
bottom = bottom




uplus :: forall (m n :: Num) . 0 <= n => UNat m -> UNat n -> UNat (m + n)
uplus UZero n = n
uplus (USuc m) n = USuc (uplus m n)



-- Well-scoped lambda terms

data Fin :: Num -> * where
  FZero :: forall (n :: Num) . 1 <= n => Fin n
  FSuc  :: forall (n :: Num) . 1 <= n => Fin (n-1) -> Fin n

data Tm :: Num -> * where
  V :: forall (m :: Num) . Fin m -> Tm m
  L :: forall (m :: Num) . 0 <= m => Tm (m+1) -> Tm m
  A :: forall (m :: Num) . 0 <= m => Tm m -> Tm m -> Tm m

idTm :: Tm 0
idTm = L (V FZero)

aTm :: Tm 1
aTm = L (A (V FZero) (V (FSuc FZero)))

weaken :: forall (m n :: Num) . 0 <= n =>
    (Fin m -> Fin n) -> Fin (m+1) -> Fin (n+1)
weaken f FZero    = FZero
weaken f (FSuc i) = FSuc (f i)

rename :: forall (m n :: Num) . 0 <= n =>
    (Fin m -> Fin n) -> Tm m -> Tm n
rename g (V i)   = V (g i)
rename g (L b)   = L (rename (weaken g) b)
rename g (A f a) = A (rename g f) (rename g a) 

foo :: forall (m n :: Num) . 0 <= n => 
    (Fin m -> Tm n) -> Fin (m+1) -> Tm (n+1)
foo g FZero = V FZero
foo g (FSuc i) = rename FSuc (g i)

subst :: forall (m n :: Num) . 0 <= n =>
    (Fin m -> Tm n) -> Tm m -> Tm n
subst g (V i)   = g i
subst g (L b)   = L (subst (foo g) b)
subst g (A f a) = A (subst g f) (subst g a)

aTm' = subst (comp V FSuc) aTm


{-
Things that would be nice:
* Let bindings or where clauses
* Underscores in patterns
* Genuine Pi-types
* More efficient constraint solving that doesn't throw away information
* Automatic translation of GADT notation into local equality constraints
* Existentials
* Mutually recursive binding groups
-}


-- A practical Haskell puzzle
-- http://www.haskell.org/pipermail/haskell-cafe/2011-February/089719.html

data Layer :: Num -> * where
  Layer0 :: forall (m :: Num) . m ~ 0 => Nat    -> Layer m
  Layer1 :: forall (m :: Num) . m ~ 1 => Nat    -> Layer m
  Layer2 :: forall (m :: Num) . m ~ 2 => Bools  -> Layer m
  Layer3 :: forall (m :: Num) . m ~ 3 => Nat    -> Layer m

deserialize :: forall (m :: Num) . m <= 3 => UNat m -> Nat -> Layer m
deserialize UZero                      n     = Layer0 n
deserialize (USuc UZero)               n     = Layer1 n
deserialize (USuc (USuc UZero))        Zero  = Layer2 TT
deserialize (USuc (USuc UZero))        n     = Layer2 FF
deserialize (USuc (USuc (USuc UZero))) n     = Layer3 n

serialize :: forall (m :: Num) . Layer m -> Nat
serialize (Layer0 n)   = n
serialize (Layer1 n)   = n
serialize (Layer2 TT)  = Zero
serialize (Layer2 FF)  = Suc Zero
serialize (Layer3 n)   = n

-- layer :: forall (m :: Num) . m <= 2 => Layer m -> Layer (m + 1)
layer :: forall (m :: Num) . Layer m -> Layer (m + 1)
layer (Layer0 n)           = Layer1 (Suc n)
layer (Layer1 (Suc Zero))  = Layer2 TT
layer (Layer1 n)           = Layer2 FF
layer (Layer2 TT)          = Layer3 Zero
layer (Layer2 FF)          = Layer3 (Suc Zero)

-- doLayers :: forall (m n :: Num) . (m + n) <= 3 => UNat n -> Layer m -> Layer (m + n)
doLayers :: forall (m n :: Num) . UNat n -> Layer m -> Layer (m + n)
doLayers UZero l    = l
doLayers (USuc n) l = doLayers n (layer l)

-- runLayers :: forall (m n :: Num) . 0 <= n, (m + n) <= 3 => UNat m -> UNat n -> Nat -> Nat
runLayers :: forall (m n :: Num) . m <= 3, (m + n) <= 3 => UNat m -> UNat n -> Nat -> Nat
runLayers m n b = serialize (doLayers n (deserialize m b))


l1  = runLayers UZero (USuc UZero) Zero
l2  = runLayers UZero (USuc (USuc UZero)) Zero
l3  = runLayers UZero (USuc (USuc (USuc UZero))) Zero
-- bad = runLayers UZero (USuc (USuc (USuc (USuc UZero)))) Zero