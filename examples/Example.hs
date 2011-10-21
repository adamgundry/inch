{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

{-
Things that would be nice:
* Pattern-matching let and lambda bindings
* Mutually recursive binding groups
* Higher-order unification
* Type synonyms
* GHC LINE pragmas that make some kind of sense
* Sigma-types
* Type-level lambda
* Type application in user syntax
* Kind inference
* Infix operators
* Coverage checking
* Module imports of some sort (Prelude in particular)
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

p1 (Pair a _) = a
p2 (Pair _ b) = b

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

vappend2 :: forall (m n :: Num) a . 0 <= m, 0 <= n =>
                Vec m a -> Vec n a -> Vec (m+n) a
vappend2 VNil ys = ys
vappend2 (VCons x xs) ys = VCons x (vappend2 xs ys)


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
fVNil        = FV VNil
fVCons x xs  = FV (VCons x (unFV xs))
fvzipWith f xs ys = FV (vzipWith f (unFV xs) (unFV ys))

fvfold :: forall (n :: Num) a (f :: Num -> *) . f 0 ->
    (forall (m :: Num) . 0 <= m => a -> f m -> f (m + 1)) -> FlipVec a n -> f n
fvfold n c xs = vfold n c (unFV xs)

vbuild :: forall (n :: Num) a . Vec n a -> Vec n a
-- vbuild xs = unFV (vfold (FV VNil) (\ y ys -> FV (VCons y (unFV ys))) xs)
vbuild = comp unFV (vfold (FV VNil) (\ y -> comp FV (comp (VCons y) unFV)))

vbuild2 = comp unFV (vfold fVNil fVCons)

-- vtranspose :: forall (n m :: Num) a . FlipVec (FlipVec a m) n -> FlipVec (FlipVec a n) m
-- vtranspose = fvfold fVNil (fvzipWith fVCons)

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


data ExPi :: (Num -> *) -> * where
  ExPi :: forall (f :: Num -> *) . pi (n :: Nat) . f n -> ExPi f

unExPi (ExPi {n} fn) = nat {n}


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



vreplicate :: forall a. pi (m :: Nat) . a -> Vec m a
vreplicate {0}   _ = VNil
vreplicate {n+1} x = VCons x (vreplicate {n} x)

vjoin :: forall a (m :: Nat) . Vec m (Vec m a) -> Vec m a
vjoin VNil                     = VNil
vjoin (VCons (VCons x xs) xss) = VCons x (vjoin (vmap vtail xss))

bindJoin :: forall (m :: * -> *) a b .
    (forall c d . (c -> d) -> m c -> m d) ->
    (forall c . m (m c) -> m c) -> m a -> (a -> m b) -> m b
bindJoin map join ma f = join (map f ma)

vectorMon {m} = Mon (vreplicate {m}) (bindJoin vmap vjoin)




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

unEven :: forall (n :: Num) . 0 <= n => Even (2 * n) -> UNat n
unEven (Twice {n}) = unat {n}



-- Something involving negative numbers

data Move :: Num -> Num -> * where
  Step :: pi (x y :: Num) . Move x y
  Join :: forall (x y x' y' :: Num) . 
            Move x y -> Move x' y' -> Move (x + x') (y + y')

runMove :: (Integer -> Integer -> Integer) -> Move 0 0 -> List (Pair Integer Integer)
runMove plus m =
  let help :: forall (x y :: Num) . Pair Integer Integer -> Move x y ->
                  Pair (Pair Integer Integer) (List (Pair Integer Integer)) 
      help (Pair a b) (Step {x} {y}) = let p = Pair (plus a x) (plus b y)
                                       in Pair p Nil
      help q (Join m1 m2) = let x = help q m1
                                y = help (p1 x) m2
                            in Pair (p1 y) (append (p2 y) (Cons (p1 x) (p2 x)))
      x = help (Pair 0 0) m
  in Cons (p1 x) (p2 x)


test = flp runMove (Join (Step {1} {2}) (Join (Step { -1} {0}) (Step {0} { -2})))


-- Something else

data Quantity :: (Num -> Num -> Num -> *) -> Num -> Num -> Num -> * where
  Q :: forall (u :: Num -> Num -> Num -> *)(m s k :: Num) . 
           Integer -> u m s k -> Quantity u m s k

multQ :: forall (q :: Num -> Num -> Num -> *)(m s k m' s' k' :: Num). 
          (q m s k -> q m' s' k' -> q (m+m') (s+s') (k+k')) ->
          (Integer -> Integer -> Integer) -> 
            Quantity q m s k ->
              Quantity q m' s' k' ->
                Quantity q (m+m') (s+s') (k+k')
multQ timesQ timesZ (Q x u) (Q y v) = Q (timesZ x y) (timesQ u v)


data Unit :: Num -> Num -> Num -> * where
  One       :: Unit 0 0 0
  Metre     :: Unit 1 0 0
  Second    :: Unit 0 1 0
  Kilogram  :: Unit 0 0 1
  Prod :: forall (m s k m' s' k' :: Num).
              Unit m s k -> Unit m' s' k' -> Unit (m + m') (s + s') (k + k')
  Inv :: forall (m s k :: Num) . 
             Unit m s k -> Unit (- m) (- s) (- k)

multU1 = multQ Prod


fivem = Q 5 Metre
sixk  = Q 6 Kilogram
thirtymk times = multU1 times fivem sixk



data Unit2 :: Num -> Num -> Num -> * where
  U2 :: pi (m s k :: Num) . Unit2 m s k

prodU2 :: forall (m s k m' s' k' :: Num).
           Unit2 m s k -> Unit2 m' s' k' -> Unit2 (m + m') (s + s') (k + k')
prodU2 (U2 {m} {s} {k}) (U2 {m'} {s'} {k'}) = U2 {m+m'} {s+s'} {k+k'}

multU2 = multQ prodU2

invU2 :: forall (m s k :: Num). Unit2 m s k -> Unit2 (-m) (-s) (-k)
invU2 (U2 {m} {s} {k}) = U2 { -m} { -s} { -k}

one2     = U2 {0} {0} {0}
metre2   = U2 {1} {0} {0}
second2  = U2 {0} {1} {0}
kilo2    = U2 {0} {0} {1}

fivem2           = Q 5 metre2
sixk2            = Q 6 kilo2
thirtymk2 times  = multU2 times fivem2 sixk2

data Unit3 :: Num -> Num -> Num -> * where
  U3 :: forall (m s k :: Num) . Unit3 m s k

prodU3 :: forall (m s k m' s' k' :: Num).
           Unit3 m s k -> Unit3 m' s' k' -> Unit3 (m + m') (s + s') (k + k')
prodU3 _ _ = U3

multU3 = multQ prodU3

invU3 :: forall (m s k :: Num). Unit3 m s k -> Unit3 (-m) (-s) (-k)
invU3 _ = U3

one3     = U3 :: Unit3 0 0 0
metre3   = U3 :: Unit3 1 0 0
second3  = U3 :: Unit3 0 1 0
kilo3    = U3 :: Unit3 0 0 1

fivem3           = Q 5 metre3
sixk3            = Q 6 kilo3
thirtymk3 times  = multU3 times fivem3 sixk3



data Bad :: (Num -> Num) -> * where
  Eek :: forall (f :: Num -> Num) . UNat (f 0) -> Bad f

-- badder :: forall (g :: Num -> Num -> Num) . Bad (g 1) -> UNat (g (2-1) 0)
-- badder (Eek n) = n


narg {n} = unat {n}





data IMon :: (Num -> * -> *) -> * where
  IMon :: forall (m :: Num -> * -> *) .
    (forall a . a -> m 0 a) ->
    (forall a b (i j :: Num) . m i a -> (a -> m j b) -> m (i+j) b) -> IMon m

iret   (IMon r _)  = r
ibind  (IMon _ b)  = b
iext   m           = flp (ibind m)
ijoin  m           = iext m (\ x -> x)





data PotList :: Num -> Num -> * -> * where
  PotNil  :: forall a (i :: Num). PotList i 0 a
  PotCons :: forall a (i j :: Num). a -> PotList i j a -> PotList i (i+j) a

attach :: forall (n :: Num) . Integer -> PotList 1 n Integer ->
              PotList 0 0 (Pair Integer Integer)
attach _ PotNil          = PotNil
attach x (PotCons y ys)  = PotCons (Pair x y) (attach x ys)




vecid :: pi (m :: Num) . forall a . Vec m a -> Vec m a
vecid {m} = let loop = loop
            in loop

natcase :: forall t . pi (m :: Num) . 0 <= m =>
               (m ~ 0 => t) ->
               (pi (n :: Num) . 0 <= n => m ~ n + 1 => t) -> t
natcase {0}    zero  _    = zero
natcase {n+1}  _     suc  = suc {n}



nateq :: forall (m n :: Num) (c :: Num -> *) . c (m + n) -> c (n + m)
nateq x = x


data EQ :: * -> * -> * where
  CONG :: forall a b . (forall (c :: * -> *) . c a -> c b) -> EQ a b

fstEq :: forall a1 a2 b1 b2 . EQ (Pair a1 b1) (Pair a2 b2) -> EQ a1 a2
fstEq (CONG f) = fstEq (CONG f)



-- Zenger's examples

sprod :: forall (n :: Num) . (Integer -> Integer -> Integer) ->
             (Integer -> Integer -> Integer) ->
             Vec n Integer -> Vec n Integer -> Integer
sprod plus times VNil VNil = 0
sprod plus times (VCons x xs) (VCons y ys) = plus (times x y) (sprod plus times xs ys)


data SplitVector :: Num -> * -> * where
  Spv :: forall (m k :: Num) a . 0 <= m, 0 <= k => Vec m a -> Vec k a -> SplitVector (m+k) a

spvLeft :: forall (n :: Num) a . a -> SplitVector n a -> SplitVector (n+1) a
spvLeft x (Spv l r) = Spv (VCons x l) r

spvRight :: forall (n :: Num) a . a -> SplitVector n a -> SplitVector (n+1) a
spvRight x (Spv l r) = Spv l (VCons x r)

spvMap :: forall (n :: Num) a b . 
          (forall (m :: Num) . Vec m a -> Vec m b) ->
          (forall (k :: Num) . Vec k a -> Vec k b) ->
          SplitVector n a -> SplitVector n b
spvMap f g (Spv l r) = Spv (f l) (g r)

spvApp :: forall (n :: Num) a . SplitVector n a -> Vec n a
spvApp (Spv l r) = vappend l r

vpartition :: forall (n :: Num) a . (a -> Bool) -> Vec n a -> SplitVector n a
vpartition f VNil = Spv VNil VNil
vpartition f (VCons x xs) | f x   = spvRight x (vpartition f xs)
vpartition f (VCons x xs) | True  = spvLeft x (vpartition f xs)
                                  
vquicksort :: forall (n :: Num) a . (a -> a -> Bool) -> Vec n a -> Vec n a
vquicksort le VNil          = VNil
vquicksort le (VCons x xs)  = spvApp (spvRight x (spvMap (vquicksort le) (vquicksort le) (vpartition (le x) xs)))


zeroVector :: pi (n :: Num) . Vec n Integer
zeroVector {0}    = VNil
zeroVector {n+1}  = VCons 0 (zeroVector {n})




data NumOrdering :: Num -> Num -> * where
  NLT :: forall (m :: Num) . pi (k :: Num) . k > 0 => NumOrdering m (m + k)
  NEQ :: forall (m :: Num) . NumOrdering m m
  NGT :: forall (n :: Num) . pi (k :: Num) . k > 0 => NumOrdering (n + k) n

{-
sucNO :: forall (m n :: Num) . NumOrdering m n -> NumOrdering (m+1) (n+1)
sucNO (NLT {k}) = NLT {k}
sucNO NEQ = NEQ
sucNO (NGT {k}) = NGT {k}

compareNum :: pi (m n :: Num) . 0 <= m, 0 <= n => NumOrdering m n
compareNum {0} {0}     = NEQ
compareNum {0} {n+1}   = NLT {n+1}
compareNum {m+1} {0}   = NGT {m+1}
compareNum {m+1} {n+1} = sucNO (compareNum {m} {n})
-}



at :: forall (m :: Num) a . Vec m a -> (pi (n :: Num) . 0 <= n, n < m => a)
at (VCons x xs) {0}    = x
at (VCons x xs) {n+1}  = at xs {n}



multcomm :: forall a . pi (m n :: Num) . (m * n ~ n * m => a) -> a
multcomm {m} {n} x = x


mkPair :: forall a b . a -> b -> (forall c. (a -> b -> c) -> c)
mkPair a b f = f a b

proj1 :: forall a b . (forall c. (a -> b -> c) -> c) -> a
proj1 p = p (\ x y -> x)

proj2 :: forall a b . (forall c. (a -> b -> c) -> c) -> b
proj2 p = p (\ x y -> y)


mkPair' :: pi (m n :: Num) . (forall c . (pi (x y :: Num) . c) -> c)
mkPair' {m} {n} f = f {m} {n}

proj1' :: (forall c . (pi (x y :: Num) . c) -> c) -> Integer
proj1' p = p (\ {m} {n} -> m)


-- Vec a m = forall (c :: Num -> *) . c 0 -> (forall (n :: Num) . a -> c n -> c (n+1)) -> c m

mkNil :: forall a (c :: Num -> *) . c 0 -> (forall (n :: Num) . a -> c n -> c (n+1)) -> c 0
mkNil nil cons = nil

mkCons :: forall a (c :: Num -> *) (m :: Num) . c 0 -> (forall (n :: Num) . a -> c n -> c (n+1)) -> a -> c m -> c (m+1)
mkCons nil cons hd tl = cons hd tl

data Off :: (Num -> *) -> (Num -> *) where
  Off :: forall (f :: Num -> *)(m :: Num) . pi (o :: Num) . f (m + o) -> Off f m

offset :: forall a (m :: Num) (c :: Num -> *) .
              (pi (n :: Num) . a -> c n -> c (n+1)) ->
                  (pi (n :: Num) . a -> Off c n -> Off c (n+1))
offset = offset

{-
appendChurch :: forall a . pi (x y :: Num) .
    (forall (c :: Num -> *) . c 0 ->
        (pi (n :: Num) . a -> c n -> c (n+1)) -> c x) ->
    (forall (c :: Num -> *) . c 0 ->
        (pi (n :: Num) . a -> c n -> c (n+1)) -> c y) ->
    (forall (c :: Num -> *) . c 0 ->
        (pi (n :: Num) . a -> c n -> c (n+1)) -> Off c (x + y))
appendChurch {x} {y} as bs nil cons = as (Off {y} (bs nil cons)) (offset cons)
-}

-- PairVec a x y = forall (c :: Num -> *) . (forall (m n :: Num) . Vec a m -> Vec a n -> c (m + n)) -> c (x + y)

data Vec' :: * -> Num -> * where
  VNil'  :: forall a. Vec' a 0
  VCons' :: forall (n :: Num) a . 0 <= n => a -> Vec' a n -> Vec' a (n+1)


mkPairVec :: forall a (x y :: Num) (c :: Num -> *) .
    Vec' a x -> Vec' a y -> (forall (m n :: Num) . Vec' a m -> Vec' a n -> c m) -> c x
mkPairVec as bs f = f as bs

fstPairVec :: forall a (x y :: Num) .
  (forall (c :: Num -> *) .
    (forall (m n :: Num) . Vec' a m -> Vec' a n -> c m)
  -> c x) -> Vec' a x
fstPairVec p = p (\ x y -> x)




elimNat :: forall a . pi (n :: Nat) .
               (n ~ 0 => a) -> 
                   (pi (m :: Nat) . n ~ m + 1 => a) ->
                       a
elimNat {0}   z s = z
elimNat {m+1} z s = s {m}


natToInt p {n} = elimNat {n} 0 (\ {m} -> p m 1)


elimNat2 :: forall (a :: Num -> *) . pi (n :: Nat) . 
              a 0 ->
              (pi (m :: Nat) . a m -> a (m + 1)) ->
              a n
elimNat2 {0}   z s = z
elimNat2 {m+1} z s = s {m} (elimNat2 {m} z s)

natToVec2 {n} = elimNat2 {n} VNil' (\ {m} -> VCons' m)


natToVec1 :: pi (n :: Nat) . Vec' Integer n
natToVec1 {n} = let f :: pi (m :: Nat) . n ~ m + 1 => Vec' Integer n
                    f {m} = VCons' m (natToVec1 {m})
                    g :: n ~ 0 => Vec' Integer n
                    g = VNil'
                in elimNat {n} g f {-(\ {m} -> VCons' m (natToVec1 {m}))-}


data Thing :: Num -> * where
  Thing :: forall (n :: Num) . Thing n

mkThing {n} = Thing :: Thing n


madNil :: forall a (m :: Num) . 0 <= m, m < 1 => Vec' a m
madNil = VNil'




data Mul :: Num -> Num -> Num -> * where
  MulBase :: forall (m :: Num) . Mul m 0 0
  MulInd :: forall (m n p :: Num) . Mul m n p -> Mul m (n+1) (p+m)

mul :: pi (m n :: Nat) . Ex (Mul m n)
mul {m} {0}   = Ex MulBase
mul {m} {n+1} = unEx (comp Ex MulInd) (mul {m} {n})

mul2 :: pi (m n :: Nat) . ExPi (Mul m n)
mul2 {m} {0}   = ExPi {0} MulBase
mul2 {m} {n+1} = 
  let
     f :: ExPi (Mul m n) -> ExPi (Mul m (n+1))
     f (ExPi {p} x) = ExPi {p+m} (MulInd x)
  in f (mul2 {m} {n})

data ExPair :: (Num -> *) -> (Num -> *) -> * where
  ExPair :: forall (f g :: Num -> *)(p :: Num) . f p -> g p -> ExPair f g

vappend' :: forall (m n :: Num) a . Vec' a m -> Vec' a n -> Vec' a (m+n)
vappend' VNil' ys = ys
vappend' (VCons' x xs) VNil' = VCons' x (vappend' xs VNil')
vappend' (VCons' x xs) (VCons' y ys) = VCons' x (vappend' xs (VCons' y ys))


vconcat :: forall a (m n :: Num) . Vec' (Vec' a m) n -> ExPair (Mul m n) (Vec' a)
vconcat VNil'            = ExPair MulBase VNil'
vconcat (VCons' xs xss)  =
    let
       f :: ExPair (Mul m (n-1)) (Vec' a) -> ExPair (Mul m n) (Vec' a)
       f (ExPair p ys) = ExPair (MulInd p) (vappend' xs ys) 
    in f (vconcat xss)





data LeibnizEq :: Num -> Num -> * where
  LEN :: forall (m n :: Num) . (forall (f :: Num -> *) . f m -> f n) ->
                                   LeibnizEq m n

-- leibnizRefl :: forall (n :: Num) . LeibnizEq n n 
leibnizRefl = LEN (\ x -> x)

-- leibnizLeibniz :: forall (f :: Num -> *)(m n :: Num) .
--                       LeibnizEq m n -> f m -> f n
leibnizLeibniz (LEN f) = f







finj :: forall (k :: Nat) . pi (n :: Nat) . Fin (n+k+1)
finj {0} = FZero
finj {m+1} = FSuc (finj {m})

{-
finwk :: forall (n :: Num) . Fin n -> Fin (n+1)
finwk FZero = FZero
finwk (FSuc i) = FSuc (finwk i)

varwk :: forall s (n :: Num) . Var s n -> Var s (n+1)
varwk (Var i) = Var (finwk i)
-}


data Var :: * -> Num -> * where
  Var :: forall (n :: Nat) s . Fin n -> Var s n

varalloc :: forall s (k :: Nat) . pi (n :: Nat) . Var s (n+k+1)
varalloc {n} = Var (finj {n})

varlookup :: forall s (n :: Nat) . Var s n -> Vec' Integer n -> Integer
varlookup (Var FZero) (VCons' x _) = x
varlookup (Var (FSuc i)) (VCons' _ xs) = varlookup (Var i) xs

varwrite :: forall s (n :: Nat) . Var s n -> Integer -> Vec' Integer n -> Vec' Integer n
varwrite (Var FZero)     k (VCons' _ xs) = VCons' k xs
varwrite (Var (FSuc i))  k (VCons' x xs) = VCons' x (varwrite (Var i) k xs)


vsnoc :: forall a (n :: Num) . Vec' a n -> a -> Vec' a (n+1)
vsnoc VNil'          a = VCons' a VNil'
vsnoc (VCons' x xs)  a = VCons' x (vsnoc xs a)


data IST :: * -> * -> Num -> * where
  Return  :: forall s a (n :: Nat) .
                 a -> IST s a n
  Bind    :: forall s a b (n :: Nat) .
                 IST s a n -> (a -> IST s b n) -> IST s b n
  Alloc   :: forall s b (n :: Nat) . 
                 Integer -> ((forall (k :: Nat) . Var s (n+k+1)) ->
                                                      IST s b (n+1)) ->
                     IST s b n
  Read    :: forall s b (n :: Nat) . 
                 Var s n -> (Integer -> IST s b n) -> IST s b n
  Write   :: forall s b (n :: Nat) . 
                 Var s n -> Integer -> IST s b n -> IST s b n
  Reset   :: forall s b (n :: Nat) . (forall s'. IST s' b 0) -> IST s b n
  Free    :: forall s b (n :: Nat) . 
                 IST s b n -> IST s b (n+1)

runIST :: forall a . (forall s . IST s a 0) -> a
runIST ist = 
  let help :: forall a s . pi (n :: Nat) . Vec' Integer n -> IST s a n -> a
      help {n} as (Return x)     = x
      help {n} as (Bind x f)     = help {n} as (f (help {n} as x))
      help {n} as (Alloc i f)    = help {n+1} (vsnoc as i)
                                                  (f (varalloc {n}))
      help {n} as (Read v f)     = help {n} as (f (varlookup v as))
      help {n} as (Write v i t)  = help {n} (varwrite v i as) t
      help {n} as (Reset t)      = help {0} VNil' t
      help {n} (VCons' _ as) (Free t) = help {n-1} as t
  in help {0} VNil' ist

prog :: forall s . (Integer -> Integer -> Integer) -> IST s Integer 0
prog plus = Alloc 3 (\ v3 ->
            Alloc 2 (\ v2 ->
            Read v3 (\ i ->
            Read v2 (\ j ->
            Write v2 (plus i j) (
            Read v2 Return
            )))))

prog2 :: forall s . IST s Integer 0
prog2 = Bind (Return 3) (\ i -> Return i)

prog3 :: forall s . IST s Integer 0
prog3 = Alloc 0 (\ v0 ->
        Reset (
        Alloc 1 (\ v1 ->
        Read v1 Return -- v0 won't typecheck
        )))

prog4 = Alloc 0 (\ v0 ->
        Free (
        Alloc 1 (\ v1 ->
        Read v0 Return -- this shouldn't work, but it does
        )))




data EndoComp :: (* -> *) -> (* -> *) -> * -> * where
  EndoComp :: forall (f g :: * -> *) x . f (g x) -> EndoComp f g x


-- TLL a f n represents f^n(a) = f (f (...(f a)...))

data TLL :: * -> (* -> *) -> Num -> * where
  TLLNil   :: forall a (f :: * -> *) . f a -> TLL a f 1
  TLLCons  :: forall a (f :: * -> *)(n :: Nat) . TLL a (EndoComp f f) n ->
                  TLL a f (n+1)

threeZero :: TLL Integer (Vec 3) 1
threeZero = TLLNil (VCons 1 (VCons 2 (VCons 3 VNil)))

twoOne :: TLL Integer (Vec 2) 2
twoOne = TLLCons (TLLNil (EndoComp (VCons (VCons 1 (VCons 2 VNil)) (VCons (VCons 3 (VCons 4 VNil)) VNil))))



data TriTrans :: (Num -> *) -> Num -> * where
  TTZero  :: forall (f :: Num -> *) . TriTrans f 0
  TTSuc   :: forall (f :: Num -> *)(n :: Nat) .
                 f n -> TriTrans f n -> TriTrans f (n+1)

-- Tri a n = TriTrans (Vec' a) n


tri :: TriTrans (Vec' Integer) 3
tri = TTSuc (VCons' 42 (VCons' 42 VNil'))
      (TTSuc (VCons' 42 VNil')
       (TTSuc VNil' TTZero))

