{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Layout where

data Ex :: (Num -> *) -> * where
  Ex :: forall (f :: Num -> *) (n :: Num) . f n -> Ex f

data Ex2 :: (Num -> *) -> (Num -> *)  -> * where
  Ex2 :: forall (f g :: Num -> *) (p :: Num) . f p -> g p -> Ex2 f g


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
  deriving Show

data K :: * -> Num -> Num -> * where
  K :: forall a . a -> K a 1 1
  deriving Show

unK :: forall a (m n :: Num) . K a m n -> a
unK (K c) = c


horizPad :: forall (s :: Num -> Num -> *) . pi (w1 d1 w2 d2 :: Nat) .
                 Layout s w1 d1 -> Layout s w2 d2 -> Layout s (w1 + w2) (max d1 d2)
horizPad {w1} {d1} {w2} {d2} l1 l2
    | {d1 > d2} = Horiz {w1} l1 (Vert {d2} l2 Empty)
    | {d1 ~ d2} = Horiz {w1} l1 l2
    | {d1 < d2} = Horiz {w1} (Vert {d1} l1 Empty) l2


stuffAt :: forall a (w d :: Num) . pi (x y :: Nat) .
    (x < w, y < d) => Layout (K a) w d -> Maybe a
stuffAt {x} {y} (Stuff (K i))       = Just i
stuffAt {x} {y} Empty               = Nothing
stuffAt {x} {y} (Horiz {wx} l1 l2) | {x <  wx} = stuffAt {x} {y} l1
                                   | {x >= wx} = stuffAt {x - wx} {y} l2
stuffAt {x} {y} (Vert {dy} l1 l2)  | {y <  dy} = stuffAt {x} {y} l1
                                   | {y >= dy} = stuffAt {x} {y - dy} l2


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

tile :: forall (s :: Num -> Num -> *) . pi (w d :: Num) . (1 <= w, 1 <= d) =>
            Layout s 1 1 -> Layout s w d
tile {1}    {1}    l = l
tile {w+2}  {1}    l = Horiz {1} l (tile {w+1} {1} l) 
tile {w}    {d+2}  l = Vert {1} (tile {w} {1} l) (tile {w} {d+1} l)



data Proxy :: Num -> * where
  Proxy :: forall (n :: Num) . Proxy n

tilen :: forall (s :: Num -> Num -> *) . 
           (forall a (m n :: Nat) . Proxy m -> Proxy n -> (0 <= m * n => a) -> a) ->
           (pi (w d x y :: Num) .
             (0 <= w, 0 <= d, 1 <= x, 1 <= y) =>
                 Layout s w d -> Layout s (w*x) (d*y))
tilen lem {w} {d} {1}    {1}    l = l
tilen lem {w} {d} {x+2}  {1}    l = lem (Proxy :: Proxy x) (Proxy :: Proxy w)
                                    (Horiz {w} l (tilen lem {w} {d} {x+1} {1} l))
tilen lem {w} {d} {x}    {y+2}  l = lem (Proxy :: Proxy x) (Proxy :: Proxy w)
                                   (lem (Proxy :: Proxy y) (Proxy :: Proxy d)
                                       (Vert {d} (tilen lem {w} {d} {x} {1} l) (tilen lem {w} {d} {x} {y+1} l)))


-- Vectors and matrices

data Vec :: * -> Num -> * where
  Nil   :: forall a . Vec a 0
  Cons  :: forall a (n :: Nat) . a -> Vec a n -> Vec a (n+1)
  deriving Show

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
  deriving Show

unM (M xss) = xss

mOne a = M (Cons (Cons (Just a) Nil) Nil)

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

render :: forall a . pi (w d :: Num) . Layout (K a) w d -> M (Maybe a) w d
render {w} {d} l =
    let
        s :: forall a . pi (w' d' :: Nat) . (K a) w' d' -> M (Maybe a) w' d'
        s {w'} {d'} (K c) = mOne c
    in foldLayout {w} {d} s (returnM Nothing) mHoriz mVert l


append [] ys = ys
append (x:xs) ys = x : append xs ys

showV :: forall (n :: Num) . Vec (Maybe Char) n -> [Char]
showV Nil                = ""
showV (Cons Nothing xs)  = ' ' : showV xs
showV (Cons (Just i) xs) = i   : showV xs

showM :: forall (w d :: Num) . M (Maybe Char) w d -> [Char]
showM (M Nil)          = ""
showM (M (Cons x xs))  = append (showV x) ('\n' : showM (M xs))

renderM {w} {d} l = showM (render {w} {d} l)



-- Cropping a w*d layout to produce a wc*dc layout starting from (x, y) 

crop :: forall (s :: Num -> Num -> *) . 
          (pi (w' d' x' y' wc' dc' :: Nat) . (x' + wc' <= w', y' + dc' <= d') =>
            s w' d' -> Layout s wc' dc') ->
          (pi (w d x y wc dc :: Nat) . (x + wc <= w, y + dc <= d) =>
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

cropK :: forall a . pi (w d x y wc dc :: Nat) . (x + wc <= w, y + dc <= d) =>
            K a w d -> Layout (K a) wc dc
cropK {w} {d} {x} {y} {wc} {dc} (K u) | {wc > 0, dc > 0}  = Stuff (K u)
cropK {w} {d} {x} {y} {wc} {dc} (K u) | True              = Empty

crop' = crop cropK


-- Overlaying two layouts so the empty bits of the second layout are transparent

overlay :: forall (s :: Num -> Num -> *) .
               (pi (w d x y wc dc :: Nat) . (x + wc <= w, y + dc <= d) =>
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

lzIn :: forall (s :: Num -> Num -> *)(w d :: Nat) . LZip s w d -> Maybe (LZip s w d)
lzIn (LZip c Empty)            = Nothing
lzIn (LZip c (Stuff s))        = Nothing
lzIn (LZip c (Horiz {x} l r))  = Just (LZip (HorizLeft {x} c r) l)
lzIn (LZip c (Vert {y} t b))   = Just (LZip (VertTop {y} c b) t)

lzOut :: forall (s :: Num -> Num -> *)(w d :: Nat) . LZip s w d -> Maybe (LZip s w d)
lzOut (LZip Root                  h) = Nothing
lzOut (LZip (HorizLeft {x} c r)   h) = Just (LZip c (Horiz {x} h r))
lzOut (LZip (HorizRight {x} l c)  h) = Just (LZip c (Horiz {x} l h))
lzOut (LZip (VertTop {y} c b)     h) = Just (LZip c (Vert {y} h b))
lzOut (LZip (VertBottom {y} t c)  h) = Just (LZip c (Vert {y} t h))

lzLeft :: forall (s :: Num -> Num -> *)(w d :: Nat) . LZip s w d -> Maybe (LZip s w d)
lzLeft (LZip (HorizRight {x} l c) h)  = Just (LZip (HorizLeft {x} c h) l)
lzLeft _                              = Nothing

lzRight :: forall (s :: Num -> Num -> *)(w d :: Nat) . LZip s w d -> Maybe (LZip s w d)
lzRight (LZip (HorizLeft {x} c r) h)  = Just (LZip (HorizRight {x} h c) r)
lzRight _                             = Nothing

lzTop :: forall (s :: Num -> Num -> *)(w d :: Nat) . LZip s w d -> Maybe (LZip s w d)
lzTop (LZip (VertBottom {x} l c) h)  = Just (LZip (VertTop {x} c h) l)
lzTop _                              = Nothing

lzBottom :: forall (s :: Num -> Num -> *)(w d :: Nat) . LZip s w d -> Maybe (LZip s w d)
lzBottom (LZip (VertTop {x} c r) h)  = Just (LZip (VertBottom {x} h c) r)
lzBottom _                           = Nothing


lzSnd :: forall (s :: Num -> Num -> *)(w d :: Num) a .
             (forall (wh dh :: Num) . Layout s wh dh -> a) ->
             LZip s w d ->
             a
lzSnd f (LZip _ l) = f l



-- Test things

l2x1 = Horiz {1} (Stuff (K 'A')) (Stuff (K 'B'))

l1xn :: forall a (n :: Num) . 1 <= n => a -> Layout (K a) 1 n
l1xn x = Vert {1} (Stuff (K x)) Empty

l1x2 :: a -> Layout (K a) 1 2
l1x2 = l1xn

grid {x} {y} a b c d = Vert {y} (Horiz {x} (Stuff a) (Stuff b))
                                (Horiz {x} (Stuff c) (Stuff d))
as {w} {d}  = tile {w} {d} (Stuff (K 'A'))
bs {w} {d}  = tile {w} {d} (Stuff (K 'B'))

abcd   = grid {1} {1} (K 'A') (K 'B') (K 'C') (K 'D')
getD   = stuffAt {1} {1} abcd
rabcd  = render {2} {2} abcd
abcdabcd   = joinLayout (grid {2} {2} abcd Empty Empty abcd)
rabcdabcd  = render {4} {4} abcdabcd




{-

instance Functor Layout where
  fmap = mapLayout

instance Monad Layout where
  (>>=)   = flip bindLayout
  return  = returnLayout

-}