{-# OPTIONS_GHC -F -pgmF ./toy #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Layout where

-- Prelude stuff

data Pair :: * -> * -> * where
  Pair :: forall a b . a -> b -> Pair a b

fstP (Pair a _) = a
sndP (Pair _ b) = b

data Option :: * -> * where
  Some :: forall a. a -> Option a
  None :: forall a.      Option a

fromSome (Some x) = x

data Ex :: (Num -> *) -> * where
  Ex :: forall (f :: Num -> *) (n :: Num) . f n -> Ex f

data Ex2 :: (Num -> *) -> (Num -> *)  -> * where
  Ex2 :: forall (f g :: Num -> *) (p :: Num) . f p -> g p -> Ex2 f g



-- Trichotomy principles

{-

triA :: forall a . pi (m n :: Num) . 0 <= m, 0 <= n =>
    (m < n => a) -> (m ~ n => a) -> (m > n => a) ->
        a
triA {0}   {n+1} a b c = a
triA {0}   {0}   a b c = b
triA {m+1} {0}   a b c = c
triA {m+1} {n+1} a b c = triA {m} {n} a b c

triB :: forall a . pi (m n :: Num) . 0 <= m, 0 <= n =>
    (m < n => a) -> (m ~ n => a) -> (m > n => a) ->
        a
triB {m} {n} a b c | {m < n} = a
triB {m} {n} a b c | {m ~ n} = b
triB {m} {n} a b c | {m > n} = c

triC :: forall (a :: Num -> Num -> *) .
    (forall (m n :: Num) . 0 <= m, m < n => a m n) ->
    (forall (m   :: Num) . 0 <= m        => a m m) ->
    (forall (m n :: Num) . 0 <= n, n < m => a m n) ->
    (forall (m n :: Num) . 0 <= m, 0 <= n => a m n -> a (m+1) (n+1)) ->
        (pi (m n :: Num) . 0 <= m, 0 <= n => a m n)
triC a b c step {0}   {n+1} = a
triC a b c step {0}   {0}   = b
triC a b c step {m+1} {0}   = c
triC a b c step {m+1} {n+1} = step (triC a b c step {m} {n})

diff :: forall a . pi (m n :: Num) . 0 <= m, 0 <= n =>
    (pi (d :: Num) . d ~ m - n => a) -> a
diff {m}   {0}   a = a {m}
diff {0}   {n}   a = a { -n }
diff {m+1} {n+1} a = diff {m} {n} a

-}

trichotomy :: forall a . pi (m n :: Num) . 0 <= m, 0 <= n =>
    (pi (d :: Num) . 0 < d, d ~ m - n => a) ->
    (n ~ m => a) ->
    (pi (d :: Num) . 0 < d, d ~ n - m => a) ->
    a
trichotomy {0}   {0}   a b c = b
trichotomy {m+1} {0}   a b c = a {m+1}
trichotomy {0}   {n+1} a b c = c {n+1}
trichotomy {m+1} {n+1} a b c = trichotomy {m} {n} a b c


-- Layout data structures

data Layout :: (Num -> Num -> *) -> Num -> Num -> * where
  Stuff :: forall (s :: Num -> Num -> *)(w d :: Nat) .
               s w d -> Layout s w d
  Empty :: forall (s :: Num -> Num -> *)(w d :: Nat) .
               Layout s w d
  Horiz :: forall (s :: Num -> Num -> *)(w d :: Nat) .
               pi (x :: Nat) . x <= w =>
                   Layout s x d -> Layout s (w-x) d -> Layout s w d
  Vert :: forall (s :: Num -> Num -> *)(w d :: Nat) .
              pi (y :: Nat) . y <= d =>
                  Layout s w y -> Layout s w (d-y) -> Layout s w d

data Ident :: * where
  A :: Ident
  B :: Ident
  C :: Ident
  D :: Ident

data K :: * -> Num -> Num -> * where
  K :: forall a . a -> K a 1 1



-- Maximum

data Max :: Num -> Num -> Num -> * where
  Less :: forall (m n :: Num) . m < n => Max m n n
  Same :: forall (m   :: Num) .          Max m m m
  More :: forall (m n :: Num) . m > n => Max m n m

stepMax :: forall (m n :: Num) . Ex (Max m n) -> Ex (Max (m+1) (n+1))
stepMax (Ex Same) = Ex Same
stepMax (Ex Less) = Ex Less
stepMax (Ex More) = Ex More

findMax :: pi (m n :: Num) . 0 <= m, 0 <= n => Ex (Max m n)
findMax {0}   {0}   = Ex Same
findMax {0}   {n+1} = Ex Less
findMax {m+1} {0}   = Ex More
findMax {m+1} {n+1} = stepMax (findMax {m} {n})


-- Horizontal composition with padding

pad :: forall (s :: Num -> Num -> *)(x y :: Nat) . 
           pi (w d :: Nat) . Layout s w d -> Layout s (w+x) (d+y)
pad {w} {d} l = Horiz {w} (Vert {d} l Empty) Empty

horizPadRight :: forall (s :: Num -> Num -> *) .
                   pi (w1 d1 w2 d2 :: Nat) . d2 <= d1 => 
                     Layout s w1 d1 -> Layout s w2 d2 -> Layout s (w1+w2) d1
horizPadRight {w1} {d1} {w2} {d2} l1 l2 = Horiz {w1} l1 (Vert {d2} l2 Empty)


{-
horizPad :: forall (s :: Num -> Num -> *) .
             pi (w1 d1 w2 d2 :: Nat) . 
               Layout s w1 d1 -> Layout s w2 d2 -> Layout s (w1 + w2) (d1 + d2)
horizPad {w1} {d1} {w2} {d2} l1 l2 = 
  let horizA :: pi (d :: Num) . 0 < d, d ~ d1 - d2 => Layout s (w1 + w2) (d1+d2)
      horizA {d} = Vert {d1} (Horiz {w1} l1 (Vert {d2} l2 Empty))
                                  Empty

      horizB :: d1 ~ d2 => Layout s (w1 + w2) (d1 + d2)
      horizB = Vert {d1} (Horiz {w1} l1 l2) Empty

      horizC :: pi (d :: Num) . 0 < d, d ~ d2 - d1 => Layout s (w1 + w2) (d1+d2)
      horizC {d} = Vert {d2} (Horiz {w1} (Vert {d1} l1 Empty) l2)
                                  Empty
  in trichotomy {d1} {d2} horizA horizB horizC

horizPad2 :: forall (s :: Num -> Num -> *) . pi (w1 d1 w2 d2 :: Nat) .
              Layout s w1 d1 -> Layout s w2 d2 -> Ex (Layout s (w1 + w2))
horizPad2 {w1} {d1} {w2} {d2} l1 l2 = 
  let horizA :: pi (d :: Num) . 0 < d, d ~ d1 - d2 => Ex (Layout s (w1 + w2))
      horizA {d} = Ex (Horiz {w1} l1 (Vert {d2} l2 Empty))

      horizB :: d1 ~ d2 => Ex (Layout s (w1 + w2))
      horizB = Ex (Horiz {w1} l1 l2)

      horizC :: pi (d :: Num) . 0 < d, d ~ d2 - d1 => Ex (Layout s (w1 + w2))
      horizC {d} = Ex (Horiz {w1} (Vert {d1} l1 Empty) l2)
  in trichotomy {d1} {d2} horizA horizB horizC
-}

horizPad3 :: forall (s :: Num -> Num -> *) . pi (w1 d1 w2 d2 :: Nat) .
                 Layout s w1 d1 -> Layout s w2 d2 ->
                     Ex2 (Max d1 d2) (Layout s (w1 + w2))
horizPad3 {w1} {d1} {w2} {d2} l1 l2 = 
  let horizA :: pi (d :: Num) . 0 < d, d ~ d1 - d2 => Ex2 (Max d1 d2) (Layout s (w1 + w2))
      horizA {d} = Ex2 More (Horiz {w1} l1 (Vert {d2} l2 Empty))

      horizB :: d1 ~ d2 => Ex2 (Max d1 d2) (Layout s (w1 + w2))
      horizB = Ex2 Same (Horiz {w1} l1 l2)

      horizC :: pi (d :: Num) . 0 < d, d ~ d2 - d1 => Ex2 (Max d1 d2) (Layout s (w1 + w2))
      horizC {d} = Ex2 Less  (Horiz {w1} (Vert {d1} l1 Empty) l2)
  in trichotomy {d1} {d2} horizA horizB horizC



-- Find the stuff at given coordinates

stuffAt :: forall a (w d :: Num) . pi (x y :: Nat) .
    x < w, y < d => Layout (K a) w d -> Option a
stuffAt {x} {y} (Stuff (K i))       = Some i
stuffAt {x} {y} Empty               = None
stuffAt {x} {y} (Horiz {wx} l1 l2)  =
    let fA :: pi (d :: Num) . 0 <= d, d ~ x - wx => Option a
        fA {d} = stuffAt {d} {y} l2

        fB :: x ~ wx => Option a
        fB = fA {0}

        fC :: pi (d :: Num) . 0 < d, d ~ wx - x => Option a
        fC {d} = stuffAt {x} {y} l1
    in trichotomy {x} {wx} fA fB fC
stuffAt {x} {y} (Vert {dy} l1 l2) =
    let fA :: pi (d :: Num) . 0 <= d, d ~ y - dy => Option a
        fA {d} = stuffAt {x} {d} l2

        fB :: y ~ dy => Option a
        fB = fA {0}

        fC :: pi (d :: Num) . 0 < d, d ~ dy - y => Option a
        fC {d} = stuffAt {x} {y} l1
    in trichotomy {y} {dy} fA fB fC


-- Layout is an indexed monad

mapLayout :: forall (s t :: Num -> Num -> *)(w d :: Num) . 
    (forall (w' d' :: Nat) . s w' d' -> t w' d') ->
        Layout s w d -> Layout t w d
mapLayout f (Stuff x)          = Stuff (f x)
mapLayout f Empty              = Empty
mapLayout f (Horiz {x} l1 l2)  = Horiz {x} (mapLayout f l1) (mapLayout f l2)
mapLayout f (Vert {y} l1 l2)   = Vert {y} (mapLayout f l1) (mapLayout f l2)

joinLayout :: forall (s :: Num -> Num -> *)(w d :: Num) .
                  Layout (Layout s) w d -> Layout s w d
joinLayout (Stuff l)          = l
joinLayout Empty              = Empty
joinLayout (Horiz {x} l1 l2)  = Horiz {x} (joinLayout l1) (joinLayout l2)
joinLayout (Vert {y} l1 l2)   = Vert {y} (joinLayout l1) (joinLayout l2)

bindLayout :: forall (s t :: Num -> Num -> *)(w d :: Num) . 
                  (forall (w' d' :: Nat) . s w' d' -> Layout t w' d') ->
                      Layout s w d -> Layout t w d
bindLayout f l = joinLayout (mapLayout f l)

returnLayout = Stuff



-- Tiling needs multiplication, otherwise it only works for 1x1 tiles

tile :: forall (s :: Num -> Num -> *) . pi (w d :: Num) . 1 <= w, 1 <= d =>
            Layout s 1 1 -> Layout s w d
tile {1}    {1}    l = l
tile {w+2}  {1}    l = Horiz {1} l (tile {w+1} {1} l) 
tile {w}    {d+2}  l = Vert {1} (tile {w} {1} l) (tile {w} {d+1} l)


-- Vectors and matrices

data Vec :: * -> Num -> * where
  Nil   :: forall a . Vec a 0
  Cons  :: forall a (n :: Nat) . a -> Vec a n -> Vec a (n+1)

vappend :: forall a (m n :: Nat) . Vec a m -> Vec a n -> Vec a (m+n)
vappend Nil          ys = ys
vappend (Cons x xs)  ys = Cons x (vappend xs ys)

vmap :: forall a b (m :: Nat) . (a -> b) -> Vec a m -> Vec b m
vmap f Nil          = Nil
vmap f (Cons x xs)  = Cons (f x) (vmap f xs)

vzipWith :: forall a b c (m :: Nat) .
                (a -> b -> c) -> Vec a m -> Vec b m -> Vec c m
vzipWith f Nil Nil = Nil
vzipWith f (Cons x xs) (Cons y ys) = Cons (f x y) (vzipWith f xs ys)

returnVec :: forall a . pi (m :: Nat) . a -> Vec a m
returnVec {0} x    = Nil
returnVec {m+1} x  = Cons x (returnVec {m} x)

data M :: * -> Num -> Num -> * where
  M :: forall a (x y :: Num) . Vec (Vec a x) y -> M a x y

unM (M xss) = xss

mOne a = M (Cons (Cons (Some a) Nil) Nil)

mHoriz :: forall a . pi (w d x :: Nat) . x <= w =>
              M a x d -> M a (w-x) d -> M a w d
mHoriz {w} {d} {x} (M l) (M r) = M (vzipWith vappend l r)

mVert :: forall a . pi (w d y :: Nat) . y <= d =>
              M a w y -> M a w (d-y) -> M a w d
mVert {w} {d} {y} (M t) (M b) = M (vappend t b)

returnM :: forall a . a -> (pi (w d :: Nat) . M a w d)
returnM x {w} {d} = M (returnVec {d} (returnVec {w} x))



-- A scary-looking fold for layouts, and an application of it to convert to matrices

foldLayout :: forall (s t :: Num -> Num -> *) a . pi (w d :: Num) . 
    (pi (w' d' :: Nat) . s w' d' -> t w' d') ->
    (pi (w' d' :: Nat) . t w' d') ->
    (pi (w' d' x :: Nat) . x <= w' => t x d' -> t (w'-x) d' -> t w' d') ->
    (pi (w' d' y :: Nat) . y <= d' => t w' y -> t w' (d'-y) -> t w' d') ->
        Layout s w d -> t w d
foldLayout {w} {d} s e h v (Stuff x) = s {w} {d} x
foldLayout {w} {d} s e h v Empty     = e {w} {d}
foldLayout {w} {d} s e h v (Horiz {x} l1 l2) =
    h {w} {d} {x} (foldLayout {x} {d} s e h v l1)
                  (foldLayout {w-x} {d} s e h v l2)
foldLayout {w} {d} s e h v (Vert {y} l1 l2) =
    v {w} {d} {y} (foldLayout {w} {y} s e h v l1)
                  (foldLayout {w} {d-y} s e h v l2)

render :: forall a . pi (w d :: Num) . Layout (K a) w d -> M (Option a) w d
render {w} {d} l =
    let
        s :: forall a . pi (w' d' :: Nat) . (K a) w' d' -> M (Option a) w' d'
        s {w'} {d'} (K c) = mOne c
    in foldLayout {w} {d} s (returnM None) mHoriz mVert l



-- Cropping a w*d layout to produce a wc*dc layout starting from (x, y) 

crop :: forall (s :: Num -> Num -> *) . 
          (pi (w' d' x' y' wc' dc' :: Nat) . x' + wc' <= w', y' + dc' <= d' =>
            s w' d' -> Layout s wc' dc') ->
          (pi (w d x y wc dc :: Nat) . x + wc <= w, y + dc <= d =>
            Layout s w d -> Layout s wc dc)
crop f {w} {d} {x} {y} {wc} {dc} (Stuff s) = f {w} {d} {x} {y} {wc} {dc} s
crop f {w} {d} {x} {y} {wc} {dc} Empty = Empty
crop f {w} {d} {x} {y} {wc} {dc} (Horiz {wx} l1 l2) | {x >= wx}
    = crop f {w-wx} {d} {x-wx} {y} {wc} {dc} l2
crop f {w} {d} {x} {y} {wc} {dc} (Horiz {wx} l1 l2) | {x + wc <= wx}
    = crop f {wx} {d} {x} {y} {wc} {dc} l1
crop f {w} {d} {x} {y} {wc} {dc} (Horiz {wx} l1 l2) | {x < wx, x + wc > wx}
    = Horiz {wx-x} (crop f {wx} {d} {x} {y} {wx-x} {dc} l1)
                   (crop f {w-wx} {d} {0} {y} {wc-(wx-x)} {dc} l2)
crop f {w} {d} {x} {y} {wc} {dc} (Vert {dy} l1 l2) | {y >= dy}
    = crop f {w} {d-dy} {x} {y-dy} {wc} {dc} l2
crop f {w} {d} {x} {y} {wc} {dc} (Vert {dy} l1 l2) | {y + dc <= dy}
    = crop f {w} {dy} {x} {y} {wc} {dc} l1
crop f {w} {d} {x} {y} {wc} {dc} (Vert {dy} l1 l2) | {y < dy, y + dc > dy}
    = Vert {dy-y} (crop f {w} {dy} {x} {y} {wc} {dy-y} l1)
                  (crop f {w} {d-dy} {x} {0} {wc} {dc-(dy-y)} l2)

cropK :: forall a . pi (w d x y wc dc :: Nat) . x + wc <= w, y + dc <= d =>
            K a w d -> Layout (K a) wc dc
cropK {w} {d} {x} {y} {wc} {dc} (K u) | {wc > 0, dc > 0}  = Stuff (K u)
cropK {w} {d} {x} {y} {wc} {dc} (K u) | True              = Empty

crop' = crop cropK


-- Overlaying two layouts so the empty bits of the second layout are transparent

overlay :: forall (s :: Num -> Num -> *) .
               (pi (w d x y wc dc :: Nat) . x + wc <= w, y + dc <= d =>
                   Layout s w d -> Layout s wc dc) ->
               (pi (w d :: Num) . 
                   Layout s w d -> Layout s w d -> Layout s w d)
overlay cropf {w} {d} l Empty                = l
overlay cropf {w} {d} Empty l'               = l'
overlay cropf {w} {d} l (Stuff s)            = Stuff s
overlay cropf {w} {d} l (Horiz {x} l1' l2')  =
    Horiz {x} (overlay cropf {x} {d} (cropf {w} {d} {0} {0} {x} {d} l) l1')
              (overlay cropf {w-x} {d} (cropf {w} {d} {x} {0} {w-x} {d} l) l2')
overlay cropf {w} {d} l (Vert {y} l1' l2')  =
    Vert {y} (overlay cropf {w} {y} (cropf {w} {d} {0} {0} {w} {y} l) l1')
             (overlay cropf {w} {d-y} (cropf {w} {d} {0} {y} {w} {d-y} l) l2')


-- Layout transformations: flipping

horizFlip :: forall (s :: Num -> Num -> *) . pi (w d :: Num) . Layout s w d -> Layout s w d
horizFlip {w} {d} Empty            = Empty
horizFlip {w} {d} (Stuff s)        = Stuff s
horizFlip {w} {d} (Horiz {x} l r)  = Horiz {w-x} r l
horizFlip {w} {d} (Vert {y} t b)   = Vert {y} (horizFlip {w} {y} t) (horizFlip {w} {d-y} b)

vertFlip :: forall (s :: Num -> Num -> *) . pi (w d :: Num) . Layout s w d -> Layout s w d
vertFlip {w} {d} Empty            = Empty
vertFlip {w} {d} (Stuff s)        = Stuff s
vertFlip {w} {d} (Horiz {x} l r)  = Horiz {x} (vertFlip {x} {d} l) (vertFlip {w-x} {d} r)
vertFlip {w} {d} (Vert {y} t b)   = Vert {d-y} b t


-- Oh no, it's a zipper

data LContext :: (Num -> Num -> *) -> Num -> Num -> Num -> Num -> * where
  Root :: forall (s :: Num -> Num -> *)(w d :: Nat) .
               LContext s w d w d
  HorizLeft :: forall (s :: Num -> Num -> *)(wr dr w d :: Nat) .
                 pi (x :: Nat) . x <= w =>
                   LContext s wr dr w d -> Layout s (w-x) d -> LContext s wr dr x d
  HorizRight :: forall (s :: Num -> Num -> *)(wr dr w d :: Nat) .
                  pi (x :: Nat) . x <= w =>
                    Layout s x d -> LContext s wr dr w d -> LContext s wr dr (w-x) d
  VertTop :: forall (s :: Num -> Num -> *)(wr dr w d :: Nat) .
                 pi (y :: Nat) . y <= d =>
                     LContext s wr dr w d -> Layout s w (d-y) -> LContext s wr dr w y
  VertBottom :: forall (s :: Num -> Num -> *)(wr dr w d :: Nat) .
                    pi (y :: Nat) . y <= d =>
                        Layout s w y -> LContext s wr dr w d -> LContext s wr dr w (d-y)

data LZip :: (Num -> Num -> *) -> Num -> Num -> * where
  LZip :: forall (s :: Num -> Num -> *)(wr dr wh dh :: Num) . 
              LContext s wr dr wh dh -> Layout s wh dh -> LZip s wr dr

lzZip = LZip Root

lzIn :: forall (s :: Num -> Num -> *)(w d :: Nat) . LZip s w d -> Option (LZip s w d)
lzIn (LZip c Empty)            = None
lzIn (LZip c (Stuff s))        = None
lzIn (LZip c (Horiz {x} l r))  = Some (LZip (HorizLeft {x} c r) l)
lzIn (LZip c (Vert {y} t b))   = Some (LZip (VertTop {y} c b) t)

lzOut :: forall (s :: Num -> Num -> *)(w d :: Nat) . LZip s w d -> Option (LZip s w d)
lzOut (LZip Root                  h) = None
lzOut (LZip (HorizLeft {x} c r)   h) = Some (LZip c (Horiz {x} h r))
lzOut (LZip (HorizRight {x} l c)  h) = Some (LZip c (Horiz {x} l h))
lzOut (LZip (VertTop {y} c b)     h) = Some (LZip c (Vert {y} h b))
lzOut (LZip (VertBottom {y} t c)  h) = Some (LZip c (Vert {y} t h))

lzLeft :: forall (s :: Num -> Num -> *)(w d :: Nat) . LZip s w d -> Option (LZip s w d)
lzLeft (LZip (HorizRight {x} l c) h)  = Some (LZip (HorizLeft {x} c h) l)
lzLeft _                              = None

lzRight :: forall (s :: Num -> Num -> *)(w d :: Nat) . LZip s w d -> Option (LZip s w d)
lzRight (LZip (HorizLeft {x} c r) h)  = Some (LZip (HorizRight {x} h c) r)
lzRight _                             = None

lzTop :: forall (s :: Num -> Num -> *)(w d :: Nat) . LZip s w d -> Option (LZip s w d)
lzTop (LZip (VertBottom {x} l c) h)  = Some (LZip (VertTop {x} c h) l)
lzTop _                              = None

lzBottom :: forall (s :: Num -> Num -> *)(w d :: Nat) . LZip s w d -> Option (LZip s w d)
lzBottom (LZip (VertTop {x} c r) h)  = Some (LZip (VertBottom {x} h c) r)
lzBottom _                           = None


lzSnd :: forall (s :: Num -> Num -> *)(w d :: Num) a .
             (forall (wh dh :: Num) . Layout s wh dh -> a) ->
             LZip s w d ->
             a
lzSnd f (LZip _ l) = f l



-- Vector patches: attempt 1

data VP :: * -> * -> * -> Num -> Num -> * where
  NilVP   :: forall x y p . VP x y p 0 0
  ConsVP  :: forall x y p (m n :: Nat) . p -> VP x y p m n -> VP x y p (m+1) (n+1)
  Ins     :: forall x y p (m n :: Nat) . y -> VP x y p m n -> VP x y p m (n+1)
  Del     :: forall x y p (m n :: Nat) . x -> VP x y p m n -> VP x y p (m+1) n

vpSource :: forall x y p (m n :: Nat) . (p -> x) -> VP x y p m n -> Vec x m
vpSource f NilVP          = Nil
vpSource f (ConsVP p vp)  = Cons (f p) (vpSource f vp)
vpSource f (Ins _ vp)     = vpSource f vp
vpSource f (Del x vp)     = Cons x (vpSource f vp)

vpDest :: forall x y p (m n :: Nat) . (p -> y) -> VP x y p m n -> Vec y n
vpDest f NilVP          = Nil
vpDest f (ConsVP p vp)  = Cons (f p) (vpDest f vp)
vpDest f (Ins y vp)     = Cons y (vpDest f vp)
vpDest f (Del _ vp)     = vpDest f vp

composeT :: forall x y z p q (m n k :: Nat) .
                (p -> x) -> (q -> z) ->
                VP x y p m n -> VP y z q n k -> VP x z (Pair p q) m k
composeT f g NilVP          NilVP          = NilVP
composeT f g xy             (Ins z yz)     = Ins z (composeT f g xy yz)
composeT f g (Del x xy)     yz             = Del x (composeT f g xy yz)
composeT f g (ConsVP p xy)  (ConsVP q yz)  = ConsVP (Pair p q) (composeT f g xy yz)
composeT f g (ConsVP p xy)  (Del y yz)     = Del (f p) (composeT f g xy yz)
composeT f g (Ins x xy)     (ConsVP q yz)  = Ins (g q) (composeT f g xy yz)
composeT f g (Ins y xy)     (Del _ yz)     = composeT f g xy yz

composeV :: forall x y p (m n m' n' :: Nat) .
                VP x y p m n -> VP x y p m' n' -> VP x y p (m+m') (n+n')
composeV NilVP          bs = bs
composeV (ConsVP p as)  bs = ConsVP p (composeV as bs)
composeV (Ins y as)     bs = Ins y (composeV as bs)
composeV (Del x as)     bs = Del x (composeV as bs)

composeH :: forall x y p x' y' p' (m n :: Nat) .
                VP x y p m n -> VP x' y' p' m n ->
                    VP (Pair x x') (Pair y y') (Pair p p') m n 
composeH NilVP NilVP                   = NilVP
composeH (ConsVP p as) (ConsVP p' bs)  = ConsVP (Pair p p') (composeH as bs)
composeH (Ins y as) (Ins y' bs)        = Ins (Pair y y') (composeH as bs)
composeH (Del x as) (Del x' bs)        = Del (Pair x x') (composeH as bs)
composeH (Ins y as) (Del x' bs)        = undefined

source2d f = vpSource (vpSource f)

dest2d :: forall x y p (m n j k :: Nat) . 
              (p -> y) -> VP (Vec x m) (Vec y n) (VP x y p m n) j k -> Vec (Vec y n) k
dest2d f = vpDest (vpDest f)


vpPure :: forall x (m :: Num) . Vec x m -> VP x x x m m 
vpPure Nil = NilVP
vpPure (Cons x xs) = ConsVP x (vpPure xs)

vpDel :: forall x y p (m n k :: Nat) . Vec x k -> VP x y p m n -> VP x y p (m+k) n
vpDel Nil          as = as
vpDel (Cons k ks)  as = Del k (vpDel ks as)

vpNorm :: forall x y p (m n k :: Nat) . Vec x k -> VP x y p (m-k) n -> VP x y p m n
vpNorm ks NilVP          = vpDel ks NilVP
vpNorm ks (ConsVP p ps)  = vpDel ks (ConsVP p (vpNorm Nil ps))
vpNorm ks (Del x ps)     = vpNorm (Cons x ks) ps
vpNorm ks (Ins y ps)     = Ins y (vpNorm ks ps)


{-
vpApp :: forall a b (m n k :: Nat) . Vec a k ->
             VP (a -> b) (a -> b) (a -> b) m n -> VP a a a (m-k) n -> VP b b b m n
vpApp Nil NilVP         NilVP          = NilVP
vpApp Nil (ConsVP f fs) (ConsVP a as)  = ConsVP (f a) (vpApp Nil fs as)
vpApp ks  (Ins f fs)    (Ins a as)     = Ins (f a) (vpApp ks fs as)
vpApp Nil (Ins f fs)    (ConsVP a as)  = vpApp Nil (Ins f fs) (Ins a (Del a as))
vpApp (Cons k ks) (Ins f fs) (ConsVP a as) = vpApp ks (Ins f fs) 
vpApp ks  (Ins f fs)    (Del a as)     = vpApp (Cons a ks) (Ins f fs) as
-}


-- Vector patches: attempt 2

data Vp :: * -> * -> * -> Num -> Num -> * where
  Vp :: forall x y p (m n ins del :: Nat) . 
            Vec x del -> Vec y ins -> MoreVp x y p m n -> Vp x y p (m+del) (n+ins)

data MoreVp :: * -> * -> * -> Num -> Num -> * where
  Stop  :: forall x y p .
               MoreVp x y p 0 0
  Go    :: forall x y p (m n :: Nat) . 
               p -> Vp x y p m n -> MoreVp x y p (m+1) (n+1)

vpSource' :: forall x y p (m n :: Nat) . (p -> x) -> Vp x y p m n -> Vec x m
vpSource' f (Vp del ins more) = vappend del (vpSourceMore f more)

vpSourceMore :: forall x y p (m n :: Nat) . (p -> x) -> MoreVp x y p m n -> Vec x m
vpSourceMore f Stop       = Nil
vpSourceMore f (Go p vp)  = Cons (f p) (vpSource' f vp)

vpDest' :: forall x y p (m n :: Num) . (p -> y) -> Vp x y p m n -> Vec y n
vpDest' f (Vp del ins more) = vappend ins (vpDestMore f more)

vpDestMore :: forall x y p (m n :: Num) . (p -> y) -> MoreVp x y p m n -> Vec y n
vpDestMore f Stop = Nil
vpDestMore f (Go p vp) = Cons (f p) (vpDest' f vp)

{-
composeT' :: forall x y z p q (m n k :: Num) . 
                (p -> x) -> (q -> z) ->
                    Vp x y p m n -> Vp y z q n k -> Vp x z (Pair p q) m k
composeT' f g (Vp xdel yins Stop)       (Vp ydel zins Stop)       =
    Vp xdel zins Stop
composeT' f g (Vp xdel yins Stop)       (Vp ydel zins (Go q yz))  =
    undefined
composeT' f g (Vp xdel yins (Go p xy))  (Vp ydel zins Stop)       =
    undefined
composeT' f g (Vp xdel yins (Go p xy))  (Vp ydel zins (Go q yz))  =
    undefined

composeTMore :: forall x y z p q (m n k ins del :: Num) . 
                    Vec y ins -> Vec y del -> 
                        MoreVp x y p m (n-ins) -> MoreVp y z q (n-del) k ->
                            Vp x z (Pair p q) m k
composeTMore yins ydel Stop Stop       = Vp Nil Nil Stop
composeTMore yins ydel Stop (Go p vp)  = undefined

vpApp' :: forall a b (m n :: Num) . 
             Vp (a -> b) (a -> b) (a -> b) m n -> Vp a a a m n ->
                 Vp b b b m n
vpApp' (Vp fdel fins fs) (Vp adel ains as) = undefined
-}


-- Test things

l2x1 = Horiz {1} (Stuff (K A)) (Stuff (K B))

l1xn :: forall (n :: Num) . 1 <= n => Layout (K Ident) 1 n
l1xn = Vert {1} (Stuff (K C)) Empty

l1x2 = l1xn :: Layout (K Ident) 1 2

grid {x} {y} a b c d = Vert {y} (Horiz {x} (Stuff a) (Stuff b))
                                (Horiz {x} (Stuff c) (Stuff d))
as {w} {d}  = tile {w} {d} (Stuff (K A))
bs {w} {d}  = tile {w} {d} (Stuff (K B))

abcd   = grid {1} {1} (K A) (K B) (K C) (K D)
getD   = stuffAt {1} {1} abcd
rabcd  = render {2} {2} abcd
abcdabcd   = joinLayout (grid {2} {2} abcd Empty Empty abcd)
rabcdabcd  = render {4} {4} abcdabcd

asbs    = horizPadRight {3} {6} {4} {2} (as {3} {6}) (bs {4} {2}) -- 7x6
rasbs   = render {7} {6} asbs
thing   = overlay (crop cropK) {7} {6} asbs (pad {4} {4} abcdabcd)
rthing  = render {7} {6} thing

vpa = Ins 3 (Del 6 (ConsVP 2 NilVP))
vpb = Ins 6 (Del 3 (ConsVP 2 NilVP))
vp2d = Ins (Cons 2 Nil) (Del Nil (ConsVP (ConsVP 3 NilVP) NilVP))
