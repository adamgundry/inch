{-# OPTIONS_GHC -F -pgmF ./toy #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures #-}

{-
Things that would be nice:
* Let bindings or where clauses
* Automatic translation of GADT notation into local equality constraints
* Mutually recursive binding groups
* Nat kind (desugars to Num with inequality constraint)
* Fix lexically-scoped type variables, without name munging
-}

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


vappend :: forall (m n :: Num) a . Vec m a -> Vec n a -> Vec (m+n) a
vappend VNil ys = ys
vappend (VCons x xs) VNil = VCons x (vappend xs VNil)
vappend (VCons x xs) (VCons y ys) = VCons x (vappend xs (VCons y ys))

vrevapp :: forall (m n :: Num) a . 0 <= n => Vec m a -> Vec n a -> Vec (m+n) a
vrevapp VNil ys = ys
vrevapp (VCons x xs) ys = vrevapp xs (VCons x ys)

vreverse :: forall (n :: Num) a . Vec n a -> Vec n a
vreverse xs = vrevapp xs VNil

vec :: forall (n :: Num) a. UNat n -> a -> Vec n a
vec UZero    a = VNil
vec (USuc m) a = VCons a (vec m a)

vec2 :: forall a. pi (n :: Num) . a -> Vec n a
vec2 {0} a = VNil
vec2 {n+1} a = VCons a (vec2 {n} a)

vid :: forall (n :: Num) a . Vec n a -> Vec n a
vid VNil          = VNil
vid (VCons x xs)  = VCons x (vid xs)

vmap :: forall (n :: Num) a b . (a -> b) -> Vec n a -> Vec n b
vmap f VNil = VNil
vmap f (VCons x xs) = VCons (f x) (vmap f xs)

vzipWith :: forall (n :: Num) a b c . (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
vzipWith f VNil VNil = VNil
vzipWith f (VCons x xs) (VCons y ys) = VCons (f x y) (vzipWith f xs ys)


vfold :: forall (n :: Num) a (f :: Num -> *) . f 0 ->
    (forall (m :: Num) . a -> f m -> f (m + 1)) -> Vec n a -> f n
-- vfold :: forall (n :: Num) a (f :: Num -> *) . f 0 ->
--    (forall (m :: Num) . 0 <= m => a -> f m -> f (m + 1)) -> Vec n a -> f n
vfold n c VNil         = n
vfold n c (VCons x xs) = c x (vfold n c xs)

vsum :: forall (n :: Num) . (Integer -> Integer -> Integer) ->
    Vec n Integer -> Integer
vsum plus VNil = 0
vsum plus (VCons x xs) = plus x (vsum plus xs)

{-
vsum2 :: forall (n :: Num) . (Integer -> Integer -> Integer) ->
    Vec n Integer -> Integer
vsum2 plus = vfold 0 plus
-}

{-
vbuild :: forall (n :: Num) a . Vec n a -> Vec n a
vbuild = vfold VNil VCons
-}


unaryToNat :: forall (n :: Num) . UNat n -> Nat
unaryToNat UZero    = Zero
unaryToNat (USuc m) = Suc (unaryToNat m)

nat :: pi (n :: Num) . 0 <= n => Nat
nat {0}   = Zero
nat {n+1} = Suc (nat {n})

plan :: pi (n :: Num) . 0 <= n => Vec n Nat
plan {0}   = VNil
plan {m+1} = VCons (nat {m}) (plan {m})

plan5 = plan {5}

vlookup :: forall (n :: Num) a . pi (m :: Num) . 0 <= m, (m+1) <= n => Vec n a -> a
vlookup {0}   (VCons x xs) = x
vlookup {k+1} (VCons x xs) = vlookup {k} xs


pairMap :: forall a b c d . (a -> c) -> (b -> d) -> Pair a b -> Pair c d
pairMap f g (Pair a b) = Pair (f a) (g b)


vsplit :: forall (n :: Num) a . pi (m :: Num) . Vec (m + n) a -> Pair (Vec m a) (Vec n a)
vsplit {0}   xs           = Pair VNil xs
vsplit {n+1} (VCons x xs) = pairMap (VCons x) i (vsplit {n} xs)

vtake :: forall (n :: Num) a . pi (m :: Num) . 0 <= m, 0 <= n => Vec (m + n) a -> Vec m a
vtake {0}   _            = VNil
vtake {i+1} (VCons x xs) = VCons x (vtake {i} xs)


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

saTm = subst (comp V FSuc) aTm



data Tm' :: Num -> * where
  V' :: forall (m :: Num) . pi (n :: Num) . 0 <= n, n <= m => Tm' m
  L' :: forall (m :: Num) . 0 <= m => Tm' (m+1) -> Tm' m
  A' :: forall (m :: Num) . Tm' m -> Tm' m -> Tm' m


idTm' :: Tm' 0
idTm' = L' (V' {0})

aTm' :: Tm' 1
aTm' = L' (A' (V' {0}) (V' {1}))

foldTm :: forall a (m :: Num) . 
    (pi (k :: Num) . a) -> (a -> a) -> (a -> a -> a) -> Tm' m -> a
foldTm v _ _ (V' {i})  = v {i}
foldTm v l a (L' b)    = l (foldTm v l a b)
foldTm v l a (A' f s)  = a (foldTm v l a f) (foldTm v l a s)

foldTm2 :: forall (a :: Num -> *) (m :: Num) . 
    (forall (k :: Num) . pi (n :: Num) . a k) ->
    (forall (k :: Num) . a (k+1) -> a k) ->
    (forall (k :: Num) . a k -> a k -> a k) ->
        Tm' m -> a m
foldTm2 v l a (V' {i}) = v {i}
foldTm2 v l a (L' b)   = l (foldTm2 v l a b)
foldTm2 v l a (A' f s) = a (foldTm2 v l a f) (foldTm2 v l a s)

{-
foldTm3 :: forall (a :: Num -> *) (m :: Num) . 
    (forall (k :: Num) . pi (n :: Num) . 0 <= n, n <= k => a k) ->
    (forall (k :: Num) . 0 <= k => a (k+1) -> a k) ->
    (forall (k :: Num) . a k -> a k -> a k) ->
        Tm' m -> a m
-}

{-
rebuildTm :: forall (m :: Num) . Tm m -> Tm m
rebuildTm = foldTm2 V' L' A'
-}



-- A practical Haskell puzzle
-- http://www.haskell.org/pipermail/haskell-cafe/2011-February/089719.html

data Layer :: Num -> * where
  Layer0 :: forall (m :: Num) . m ~ 0 => Nat    -> Layer m
  Layer1 :: forall (m :: Num) . m ~ 1 => Nat    -> Layer m
  Layer2 :: forall (m :: Num) . m ~ 2 => Bools  -> Layer m
  Layer3 :: forall (m :: Num) . m ~ 3 => Nat    -> Layer m

deserialize :: pi (m :: Num) . m <= 3 => Nat -> Layer m
deserialize {0} n     = Layer0 n
deserialize {1} n     = Layer1 n
deserialize {2} Zero  = Layer2 TT
deserialize {2} n     = Layer2 FF
deserialize {3} n     = Layer3 n

serialize :: forall (m :: Num) . Layer m -> Nat
serialize (Layer0 n)   = n
serialize (Layer1 n)   = n
serialize (Layer2 TT)  = Zero
serialize (Layer2 FF)  = Suc Zero
serialize (Layer3 n)   = n

layer :: forall (m :: Num) . m <= 2 => Layer m -> Layer (m + 1)
layer (Layer0 n)           = Layer1 (Suc n)
layer (Layer1 (Suc Zero))  = Layer2 TT
layer (Layer1 n)           = Layer2 FF
layer (Layer2 TT)          = Layer3 Zero
layer (Layer2 FF)          = Layer3 (Suc Zero)

doLayers :: forall (m :: Num) . pi (n :: Num) . 0 <= m, 0 <= n, (m + n) <= 3 => Layer m -> Layer (m + n)
doLayers {0}   l = l
doLayers {i+1} l = doLayers {i} (layer l)

runLayers :: pi (m n :: Num) . 0 <= m, 0 <= n, (m + n) <= 3 => Nat -> Nat
runLayers {m} {n} b = serialize (doLayers {n} (deserialize {m} b))


l1  = runLayers {0} {1} Zero
l2  = runLayers {0} {2} Zero
l3  = runLayers {0} {3} Zero



-- Cartesian

data Coord :: Num -> Num -> Num -> Num -> * where
  Coord :: pi (l b r t :: Num) . l <= r, b <= t => Coord l b r t

data Shape :: Num -> Num -> Num -> Num -> * where
  Box :: pi (l b r t :: Num) . l <= r, b <= t => Shape l b r t
  Above :: forall (l b r t b' :: Num) . Shape l b r t -> Shape l b' r b -> Shape l b' r t

point :: pi (x y :: Num) . Shape x y x y
point {x} {y} = Box {x} {y} {x} {y}


box1 = Box {0} {0} {1} {1}
box2 = Box {0} {1} {1} {3}
boxes = Above box2 box1


aboveC :: forall (l b r t b' :: Num) . Coord l b r t ->
    Coord l b' r b -> Coord l b' r t
aboveC (Coord {l} {b} {r} {t}) (Coord {l2} {b'} {r2} {t2}) =
    Coord {l} {b'} {r} {t} 

bound :: forall (l b r t :: Num) . Shape l b r t -> Coord l b r t
bound (Box {l} {b} {r} {t}) = Coord {l} {b} {r} {t}
bound (Above s t) = aboveC (bound s) (bound t)



-- Existentials

data Ex :: (Num -> *) -> * where
  Ex :: forall (f :: Num -> *) (n :: Num) . f n -> Ex f

unEx :: forall (f :: Num -> *) a . (forall (n :: Num) . f n -> a) -> Ex f -> a
unEx g (Ex x) = g x

data IntVec :: Num -> * where
  IV :: forall (n :: Num) . Vec n Integer -> IntVec n

len :: Ex IntVec -> Nat
len (Ex (IV VNil))         = Zero
len (Ex (IV (VCons x xs))) = Suc (len (Ex (IV (VCons x xs))))

ivappend :: Ex IntVec -> Ex IntVec -> Ex IntVec
ivappend (Ex (IV xs)) (Ex (IV ys)) = Ex (IV (vappend xs ys))


data ExPi where
  ExPi :: pi (n :: Num) . 0 <= n => ExPi

unExPi (ExPi {n+1})  = Suc (unExPi (ExPi {n}))
unExPi (ExPi {0})    = Zero

unExPi2 (ExPi {n}) = nat {n}


data ExSet :: (* -> *) -> * where
  ExSet :: forall (f :: * -> *) a . f a -> ExSet f

unExSet :: forall (f :: * -> *) b . (forall a . f a -> b) -> ExSet f -> b
unExSet g (ExSet x) = g x

data SillyPair :: * -> * where
  SillyPair :: forall a . a -> (a -> Integer) -> SillyPair a

unSP :: ExSet SillyPair -> Integer
unSP (ExSet (SillyPair a f)) = f a
