{-# OPTIONS_GHC -F -pgmF ./toy #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables #-}

module Layout where

bottom = bottom


data Ident :: * where
  A :: Ident
  B :: Ident
  C :: Ident


data Stuff :: Num -> Num -> * where
  Unit :: forall (w d :: Num) . w ~ 1, d ~ 1 => Ident -> Stuff w d

data Layout :: Num -> Num -> * where
  Stuff :: forall (w d :: Num) . 0 <= w, 0 <= d => Stuff w d -> Layout w d
  Empty :: forall (w d :: Num) . 0 <= w, 0 <= d => Layout w d
  Horiz :: forall (w d :: Num) . 0 <= w, 0 <= d => 
    pi (w1 w2 :: Num) . 0 <= w1, 0 <= w2, w ~ (w1 + w2) =>
    Layout w1 d -> Layout w2 d -> Layout w d
  Vert :: forall (w d :: Num) . 0 <= w, 0 <= d => 
    pi (d1 d2 :: Num) . 0 <= d1, 0 <= d2, d ~ (d1 + d2) =>
    Layout w d1 -> Layout w d2 -> Layout w d


trichotomy :: forall a . pi (m n :: Num) . 0 <= m, 0 <= n =>
    (m < n => a) -> (m ~ n => a) -> (m > n => a) ->
        a
trichotomy {0}   {n+1} a b c = a
trichotomy {0}   {0}   a b c = b
trichotomy {m+1} {0}   a b c = c
trichotomy {m+1} {n+1} a b c = trichotomy {m} {n} a b c


tric2 :: forall (a :: Num -> Num -> *) .
    (forall (m n :: Num) . 0 <= m, m < n => a m n) ->
    (forall (m   :: Num) . 0 <= m        => a m m) ->
    (forall (m n :: Num) . 0 <= n, n < m => a m n) ->
        (pi (m n :: Num) . 0 <= m, 0 <= n => a m n)
tric2 a b c {0}   {n+1} = a
tric2 a b c {0}   {0}   = b
tric2 a b c {m+1} {0}   = c
tric2 a b c {m+1} {n+1} = tric2 a b c {m} {n}


l2x1 = Horiz {1} {1} (Stuff (Unit A)) (Stuff (Unit B))

l1xn :: pi (n :: Num) . 1 <= n => Layout 1 n
l1xn {n} = Vert {1} {n-1} (Stuff (Unit C)) Empty

l1x2 = l1xn {2}


diff :: forall a . pi (m n :: Num) . 0 <= m, 0 <= n =>
    (pi (d :: Num) . d ~ m - n => a) -> a
diff {m}   {0}   a = a {m}
diff {0}   {n}   a = a { -n }
diff {m+1} {n+1} a = diff {m} {n} a

tric3 :: forall a . pi (m n :: Num) . 0 <= m, 0 <= n =>
    (pi (d :: Num) . 0 < d, d ~ m - n => a) ->
    (n ~ m => a) ->
    (pi (d :: Num) . 0 < d, d ~ n - m => a) ->
    a
tric3 {0}   {0}   a b c = b
tric3 {m+1} {0}   a b c = a {m+1}
tric3 {0}   {n+1} a b c = c {n+1}
tric3 {m+1} {n+1} a b c = tric3 {m} {n} a b c


{-
horiz :: pi (w1 w2 d1 d2 :: Num) . 0 <= w1, 0 <= w2, 0 <= d1, 0 <= d2 =>
    Layout w1 d1 -> Layout w2 d2 -> Layout (w1 + w2) d1
horiz {w1} {w2} {d1} {d2} l1 l2 = 
  let horizA :: pi (d :: Num) . 0 < d, d ~ d1 - d2 => Layout (w1 + w2) d1
      horizA {d} = Horiz {w1} {w2} l1 (Vert {d2} {d} l2 Empty)

      horizC :: pi (d :: Num) . 0 < d, d ~ d2 - d1 => Layout (w1 + w2) d2
      horizC {d} = Horiz {w1} {w2} (Vert {d1} {d} l1 Empty) l2
  in tric3 {d1} {d2} horizA (Horiz {w1} {w2} l1 l2) horizC
-}

horiz :: pi (w1 w2 d1 d2 :: Num) . 0 <= w1, 0 <= w2, 0 <= d1, 0 <= d2 =>
    Layout w1 d1 -> Layout w2 d2 -> Layout (w1 + w2) (d1+d2)
horiz {w1} {w2} {d1} {d2} l1 l2 = 
  let horizA :: pi (d :: Num) . 0 < d, d ~ d1 - d2 => Layout (w1 + w2) (d1+d2)
      horizA {d} = Vert {d1} {d2} (Horiz {w1} {w2} l1 (Vert {d2} {d} l2 Empty))
                                  Empty

      horizB :: d1 ~ d2 => Layout (w1 + w2) (d1 + d2)
      horizB = Vert {d1} {d1} (Horiz {w1} {w2} l1 l2) Empty

      horizC :: pi (d :: Num) . 0 < d, d ~ d2 - d1 => Layout (w1 + w2) (d1+d2)
      horizC {d} = Vert {d2} {d1} (Horiz {w1} {w2} (Vert {d1} {d} l1 Empty) l2)
                                  Empty
  in tric3 {d1} {d2} horizA horizB horizC




data Max :: Num -> Num -> Num -> * where
  Less :: forall (m n d :: Num) . m < n, m ~ d => Max m n d
  Same :: forall (m n d :: Num) . m ~ d, n ~ d => Max m n d
  More :: forall (m n d :: Num) . m > n, n ~ d => Max m n d

data Ex :: (Num -> *) -> * where
  Ex :: forall (f :: Num -> *) (n :: Num) . f n -> Ex f

findMax :: pi (m n :: Num) . 0 <= m, 0 <= n => Ex (Max m n)
findMax {0}   {0}   = Ex Same
findMax {0}   {n+1} = Ex Less
findMax {m+1} {0}   = Ex More
findMax {m+1} {n+1} = findMax {m} {n} -- why does this typecheck?


horiz2 :: pi (w1 w2 d1 d2 :: Num) . 0 <= w1, 0 <= w2, 0 <= d1, 0 <= d2 =>
    Layout w1 d1 -> Layout w2 d2 -> Ex (Layout (w1 + w2))
horiz2 {w1} {w2} {d1} {d2} l1 l2 = 
  let horizA :: pi (d :: Num) . 0 < d, d ~ d1 - d2 => Ex (Layout (w1 + w2))
      horizA {d} = Ex (Horiz {w1} {w2} l1 (Vert {d2} {d} l2 Empty))

      horizB :: d1 ~ d2 => Ex (Layout (w1 + w2))
      horizB = Ex (Horiz {w1} {w2} l1 l2)

      horizC :: pi (d :: Num) . 0 < d, d ~ d2 - d1 => Ex (Layout (w1 + w2))
      horizC {d} = Ex (Horiz {w1} {w2} (Vert {d1} {d} l1 Empty) l2)
  in tric3 {d1} {d2} horizA horizB horizC



data Option :: * -> * where
  Some :: forall a. a -> Option a
  None :: forall a. Option a


identAt :: forall (w d :: Num) . pi (x y :: Num) .
    0 <= x, 0 <= y, x < w, y < d => Layout w d -> Option Ident
identAt {x} {y} (Stuff (Unit i)) = Some i
identAt {x} {y} Empty            = None
identAt {x} {y} (Horiz {w1} {w2} l1 l2) =
    let fA :: pi (d :: Num) . 0 < d, d ~ x - w1 => Option Ident
        fA {d} = identAt {d} {y} l2

        fB :: x ~ w1 => Option Ident
        fB = None

        fC :: pi (d :: Num) . 0 < d, d ~ w1 - x => Option Ident
        fC {d} = identAt {x} {y} l1
    in tric3 {x} {w1} fA fB fC
identAt {x} {y} (Vert {d1} {d2} l1 l2) =
    let fA :: pi (d :: Num) . 0 < d, d ~ y - d1 => Option Ident
        fA {d} = identAt {x} {d} l2

        fB :: y ~ d1 => Option Ident -- x ~ w1 works???
        fB = None

        fC :: pi (d :: Num) . 0 < d, d ~ d1 - y => Option Ident
        fC {d} = identAt {x} {y} l1
    in tric3 {y} {d1} fA fB fC