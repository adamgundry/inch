{-# OPTIONS_GHC -F -pgmF ./toy #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

{-
Things that would be nice:
* Fix existential numeric types bug
* Better representation of lexical type variable scope
* Pattern-matching let and lambda bindings
* Mutually recursive binding groups
* Nat kind (desugars to Num with inequality constraint)
* Higher-order unification
* Type synonyms
* GHC LINE pragmas that make some kind of sense
* Sigma-types
* Type-level lambda
* Type application in user syntax
-}

module Example where

-- Combinators

k        = \ x y -> x
s x y z  = x z (y z)
i        = s k k 
app f s  = f s
comp f g = \ x -> f (g x)
fix f    = f (fix f)
flp      = \ f x y -> f y x

-- Data types

data Pair :: * -> * -> * where
  Pair :: forall a b. a -> b -> Pair a b

data Nat where
  Zero :: Nat
  Suc :: Nat -> Nat



-- Booleans

andy True True = True
andy _ _       = False

silly x | andy x x = False
silly x | True = True



data Vec :: Num -> * -> * where
  VNil :: forall a. Vec 0 a
  VCons :: forall (n :: Num) a . 0 <= n => a -> Vec n a -> Vec (n+1) a

{-
data Vec :: Num -> * -> * where
  VNil :: forall (n :: Num) a . n ~ 0 => Vec n a
  VCons :: forall (n m :: Num) a . 1 <= n => a -> Vec (n-1) a -> Vec n a
-}

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
    (forall (m :: Num) . 0 <= m => a -> f m -> f (m + 1)) -> Vec n a -> f n
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


data FlipVec :: * -> Num -> * where
  FV :: forall a (n :: Num) . Vec n a -> FlipVec a n   

unFV (FV xs) = xs

vbuild :: forall (n :: Num) a . Vec n a -> Vec n a
-- vbuild xs = unFV (vfold (FV VNil) (\ y ys -> FV (VCons y (unFV ys))) xs)
vbuild = comp unFV (vfold (FV VNil) (\ y -> comp FV (comp (VCons y) unFV)))

{-
vbuild2 :: forall (n :: Num) a . Vec n a -> Vec n a
vbuild2 = vfold VNil VCons
-}

unat :: pi (n :: Num) . 0 <= n => UNat n
unat {0}   = UZero
unat {n+1} = USuc (unat {n})

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

{-
vsplit2 :: forall (n :: Num) a . pi (m :: Num) . Vec (m + n) a -> Pair (Vec m a) (Vec n a)
vsplit2 {0}   xs           = Pair VNil xs
vsplit2 {n+1} (VCons x xs) = let  f (Pair ys zs)  = Pair (VCons x ys) zs
                                  xs'             = vsplit2 {n} xs
                             in f xs'
-}

vtake :: forall (n :: Num) a . pi (m :: Num) . 0 <= m, 0 <= n => Vec (m + n) a -> Vec m a
vtake {0}   _            = VNil
vtake {i+1} (VCons x xs) = VCons x (vtake {i} xs)


one      = Suc Zero
two      = Suc one
three    = Suc two
v123     = VCons one (VCons two (VCons three VNil))
right    = vhead v123
righter  = app vtail v123



uplus :: forall (m n :: Num) . 0 <= n => UNat m -> UNat n -> UNat (m + n)
uplus UZero n = n
uplus (USuc m) n = USuc (uplus m n)



-- Well-scoped lambda terms

data Fin :: Num -> * where
  FZero :: forall (n :: Num) . 1 <= n => Fin n
  FSuc  :: forall (n :: Num) . Fin n -> Fin (n+1)

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


foldTm3 :: forall (a :: Num -> *) (m :: Num) . 
    (forall (k :: Num) . pi (n :: Num) . 0 <= n, n <= k => a k) ->
    (forall (k :: Num) . 0 <= k => a (k+1) -> a k) ->
    (forall (k :: Num) . a k -> a k -> a k) ->
        Tm' m -> a m
foldTm3 v l a (V' {i}) = v {i}
foldTm3 v l a (L' b) = l (foldTm3 v l a b)
foldTm3 v l a (A' f s) = a (foldTm3 v l a f) (foldTm3 v l a s)


rebuildTm :: forall (m :: Num) . Tm' m -> Tm' m
rebuildTm = foldTm3 V' L' A'



-- A practical Haskell puzzle
-- http://www.haskell.org/pipermail/haskell-cafe/2011-February/089719.html

data Layer :: Num -> * where
  Layer0 :: Nat   -> Layer 0
  Layer1 :: Nat   -> Layer 1
  Layer2 :: Bool  -> Layer 2
  Layer3 :: Nat   -> Layer 3

deserialize :: pi (m :: Num) . 0 <= m, m <= 3 => Nat -> Layer m
deserialize {0} n     = Layer0 n
deserialize {1} n     = Layer1 n
deserialize {2} Zero  = Layer2 True
deserialize {2} n     = Layer2 False
deserialize {3} n     = Layer3 n

serialize :: forall (m :: Num) . Layer m -> Nat
serialize (Layer0 n)   = n
serialize (Layer1 n)   = n
serialize (Layer2 True)  = Zero
serialize (Layer2 False)  = Suc Zero
serialize (Layer3 n)   = n

layer :: forall (m :: Num) . m <= 2 => Layer m -> Layer (m + 1)
layer (Layer0 n)           = Layer1 (Suc n)
layer (Layer1 (Suc Zero))  = Layer2 True
layer (Layer1 n)           = Layer2 False
layer (Layer2 True)        = Layer3 Zero
layer (Layer2 False)       = Layer3 (Suc Zero)

doLayers :: forall (m :: Num) . pi (n :: Num) .
    0 <= m, 0 <= n, (m + n) <= 3 => Layer m -> Layer (m + n)
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
  Above :: forall (l b r t b' :: Num) .
             Shape l b r t -> Shape l b' r b -> Shape l b' r t

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

unEx :: forall (f :: Num -> *) a .
            (forall (n :: Num) . f n -> a) -> Ex f -> a
unEx g (Ex x) = g x

mapEx :: forall (f g :: Num -> *) .
             (forall (n :: Num) . f n -> g n) -> Ex f -> Ex g
mapEx g (Ex x) = Ex (g x)


len :: forall a. Ex (FlipVec a) -> Nat
len (Ex (FV VNil))         = Zero
len (Ex (FV (VCons x xs))) = Suc (len (Ex (FV (VCons x xs))))

evappend (Ex (FV xs)) (Ex (FV ys)) = Ex (FV (vappend xs ys))
evmap f = mapEx (comp FV (comp (vmap f) unFV))
evsing x = Ex (FV (VCons x VNil))

evconcat (Ex (FV VNil)) = Ex (FV VNil)
evconcat (Ex (FV (VCons xs xss))) = evappend xs (evconcat (Ex (FV xss)))


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


-- Local let binding and other random stuff

f x = let y z = x
          a = a
      in y (x a)

localLet = let i x  = x
               j    = \ x -> x
           in (i i) (j j)

rank2 :: (forall a . a -> a) -> Integer
rank2 = \ f -> f f f 0


predtrans :: (pi (n :: Num) . 0 <= n => Bool) -> (pi (n :: Num) . 0 <= n => Bool)
predtrans p {0}   = True
predtrans p {n+1} = let andy True True = True
                        andy _ _ = False
                    in andy (predtrans p {n}) (p {n})

peven :: pi (n :: Num) . 0 <= n => Bool
peven {0} = True
peven {1} = False
peven {n+2} = peven {n}


thingy :: (pi (n :: Num) . 0 <= n => forall a. a -> Vec n a) -> Vec 5 Integer
thingy f = f {5} 42

vec' :: pi (n :: Num) . 0 <= n => forall a . a -> Vec n a
vec' {n} a = vec2 {n} a

useThingy   = thingy vec'
useThingy2  = thingy vec2

rank3 :: forall b. ((forall a. a) -> b) -> b
rank3 f = let loop = loop
          in f loop

 
functorCompose :: forall (f g :: * -> *) .
    (forall a b . (a -> b) -> f a -> f b) ->
    (forall a b . (a -> b) -> g a -> g b) ->
    (forall a b . (a -> b) -> f (g a) -> f (g b))
functorCompose fmap gmap = comp fmap gmap



-- Typeclass encoding (higher rank goodness)

data Mon :: (* -> *) -> * where
  Mon :: forall (m :: * -> *) . (forall a . a -> m a) ->
             (forall a b . m a -> (a -> m b) -> m b) -> Mon m

ret (Mon r b) = r
bnd (Mon r b) = b
ext (Mon r b) f ma = b ma f

monMap :: forall (m :: * -> *) a b . Mon m -> (a -> b) -> (m a -> m b)
monMap (Mon ret bnd) f = ext (Mon ret bnd) (comp ret f)


readerMon :: forall t. Mon ((->) t)
readerMon = Mon (\ a b -> a) (\ f g t -> g (f t) t) 


data List :: * -> * where
  Nil  :: forall a. List a
  Cons :: forall a. a -> List a -> List a

listMap :: forall a b. (a -> b) -> List a -> List b
listMap f Nil = Nil
listMap f (Cons x xs) = Cons (f x) (listMap f xs)

listListAlmostMap = functorCompose listMap
listListMap = listListAlmostMap listMap

append :: forall a. List a -> List a -> List a
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

listConcat :: forall a. List (List a) -> List a
listConcat Nil = Nil
listConcat (Cons xs xss) = append xs (listConcat xss)



data Comp :: ((Num -> *) -> *) -> (* -> Num -> *) -> * -> * where
  C :: forall (g :: (Num -> *) -> *) x (f :: (* -> Num -> *)).
           g (f x) -> Comp g f x

unC (C a) = a

listMon :: Mon (Comp Ex FlipVec)
listMon = Mon (comp C evsing) (\ xs f -> C (evconcat (evmap (comp unC f) (unC xs))))


trav :: forall (m :: * -> *) a b . Mon m -> (a -> m b) -> List a -> m (List b)
trav (Mon ret bnd) f Nil = ret Nil
trav (Mon ret bnd) f (Cons x xs) = bnd (f x) (\ y -> 
    bnd (trav (Mon ret bnd) f xs) (\ ys -> ret (Cons y ys)))
-- trav m f (Cons x xs) = bnd m (f x) (\ y -> 
--     bnd m (trav m f xs) (\ ys -> ret m (Cons y ys)))


-- Predicates

data EqNum :: Num -> Num -> * where
  Refl :: forall (n :: Num) . EqNum n n

leibniz :: forall (f :: Num -> *) (m n :: Num) . EqNum m n -> f m -> f n
leibniz Refl = id

trans :: forall (m n p :: Num) . EqNum m n -> EqNum n p -> EqNum m p
trans Refl Refl = Refl


data Even :: Num -> * where
  Twice :: pi (n :: Num) . Even (2 * n)

unEven (Twice {n}) = unat {n}