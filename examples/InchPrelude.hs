{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables #-}

module InchPrelude where

import Prelude hiding (subtract, id, const, flip, maybe, either,
                         curry, uncurry, until, asTypeOf, map, filter,
                         concat, concatMap, head, tail, last, init,
                         null, length, foldl, foldl1, scanl, scanl1,
                         foldr, foldr1, iterate, repeat, replicate,
                         take, drop, splitAt, takeWhile, unlines,
                         unwords, reverse, and, or, any, all, sum,
                         product, maximum, minimum, zip, zipWith,
                         zipWith3, cycle, map, fst, snd, error,
                         undefined)

-- Numeric functions


subtract         :: Integer -> Integer -> Integer
subtract         =  flip (-)

{-
even             :: Integer -> Bool
odd              :: Integer -> Bool
even n           =  rem n 2 == 0
odd              =  not . even


gcd              :: (Integral a) => a -> a -> a
gcd 0 0          =  error "Prelude.gcd: gcd 0 0 is undefined"
gcd x y          =  gcd' (abs x) (abs y)
                    where gcd' x 0  =  x
                          gcd' x y  =  gcd' y (x `rem` y)


lcm              :: (Integral a) => a -> a -> a
lcm _ 0          =  0
lcm 0 _          =  0
lcm x y          =  abs ((x `quot` (gcd x y)) * y)


(^)              :: (Num a, Integral b) => a -> b -> a
x ^ 0            =  1
x ^ n | n > 0    =  f x (n-1) x
                    where f _ 0 y = y
                          f x n y = g x n  where
                                    g x n | even n  = g (x*x) (n `quot` 2)
                                          | otherwise = f x (n-1) (x*y)
_ ^ _            = error "Prelude.^: negative exponent"


(^^)             :: (Fractional a, Integral b) => a -> b -> a
x ^^ n           =  if n >= 0 then x^n else recip (x^(-n))

-}

id               :: a -> a
id x             =  x

const            :: a -> b -> a
const x _        =  x

-- should be (.)
comp              :: (b -> c) -> (a -> b) -> a -> c
comp f g            =  \ x -> f (g x)

flip             :: (a -> b -> c) -> b -> a -> c
flip f x y       =  f y x


{-
($), ($!) :: (a -> b) -> a -> b
f $  x    =  f x
f $! x    =  x `seq` f x
-}


-- built in
data  Bool' where
     False' :: Bool'
     True' :: Bool'
   deriving (Eq, Ord, Enum, Read, Show, Bounded)



-- should be (&&)
amp              :: Bool -> Bool -> Bool
amp True x       =  x
amp False _      =  False

-- should be (||)
bar True _       =  True
bar False x      =  x
                                    

-- built in
not'              :: Bool -> Bool
not' True         =  False
not' False        =  True

otherwise'        :: Bool
otherwise'        =  True



-- built in
data  Maybe' :: * -> * where
    Nothing'  :: Maybe' a
    Just'     :: a -> Maybe' a
  deriving (Eq, Ord, Read, Show)

maybe              :: b -> (a -> b) -> Maybe a -> b
maybe n f Nothing  =  n
maybe n f (Just x) =  f x



-- built in
data  Either' :: * -> * -> * where
    Left'   :: a -> Either' a b
    Right'  :: b -> Either' a b
  deriving (Eq, Ord, Read, Show)

either               :: (a -> c) -> (b -> c) -> Either a b -> c
either f g (Left x)  =  f x
either f g (Right y) =  g y



-- built in
data  Ordering' where
    LT' :: Ordering'
    EQ' :: Ordering'
    GT' :: Ordering'
  deriving (Eq, Ord, Enum, Read, Show, Bounded)


numericEnumFrom         :: Integer -> [Integer]

numericEnumFromThen     :: Integer -> Integer -> [Integer]

-- numericEnumFromTo       :: Integer -> Integer -> [Integer]
-- numericEnumFromThenTo   :: Integer -> Integer -> Integer -> [Integer]

numericEnumFrom         =  iterate (\ x -> x + 1)
numericEnumFromThen n m =  iterate (\ x -> x + (m-n)) n


{-
numericEnumFromTo n m   =  takeWhile (<= m+1/2) (numericEnumFrom n)
numericEnumFromThenTo n n' m = takeWhile p (numericEnumFromThen n n')
                             where
                               p | n' >= n   = (<= m + (n'-n)/2)
                                 | otherwise = (>= m + (n'-n)/2)
-}




{-
-- Illegal Haskell
data  [a]  =  [] | a : [a]  deriving (Eq, Ord)
data  (a,b)   =  (a,b)    deriving (Eq, Ord, Bounded)
-}

fst              :: (a,b) -> a
fst (x,y)        =  x

snd              :: (a,b) -> b
snd (x,y)        =  y

curry            :: ((a, b) -> c) -> a -> b -> c
curry f x y      =  f (x, y)

uncurry          :: (a -> b -> c) -> ((a, b) -> c)
uncurry f p      =  f (fst p) (snd p)

until            :: (a -> Bool) -> (a -> a) -> a -> a
until p f x 
     | p x       =  x
     | otherwise =  until p f (f x)

asTypeOf         :: a -> a -> a
asTypeOf         =  const

error            :: [Char] -> a
error            =  error

undefined        :: a
undefined        =  error "Prelude.undefined"

map :: (a -> b) -> [a] -> [b]
map f []     = []
map f (x:xs) = f x : map f xs

-- should be (++)
append :: [a] -> [a] -> [a]
append []     ys = ys
append (x:xs) ys = x : append xs ys

filter :: (a -> Bool) -> [a] -> [a]
filter p []                 = []
filter p (x:xs) | p x       = x : filter p xs
                | otherwise = filter p xs

concat :: [[a]] -> [a]
concat xss = foldr append [] xss


concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f = comp concat (map f)

head             :: [a] -> a
head (x:_)       =  x
head []          =  error "Prelude.head: empty list"

tail             :: [a] -> [a]
tail ((:) _ xs)  =  xs
tail []          =  error "Prelude.tail: empty list"

last             :: [a] -> a
last [x]         =  x
last ((:) _ xs)  =  last xs
last []          =  error "Prelude.last: empty list"

init             :: [a] -> [a]
init [x]         =  []
init (x:xs)      =  x : init xs
init []          =  error "Prelude.init: empty list"

null             :: [a] -> Bool
null []          =  True
null ((:) _ _)   =  False

length           :: [a] -> Integer
length []        =  0
length ((:) _ l) =  1 + length l


{-
(!!)                :: [a] -> Int -> a
xs     !! n | n < 0 =  error "Prelude.!!: negative index"
[]     !! _         =  error "Prelude.!!: index too large"
(x:_)  !! 0         =  x
(_:xs) !! n         =  xs !! (n-1)
-}



foldl            :: (a -> b -> a) -> a -> [b] -> a
foldl f z []     =  z
foldl f z (x:xs) =  foldl f (f z x) xs


foldl1           :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs)  =  foldl f x xs
foldl1 _ []      =  error "Prelude.foldl1: empty list"

scanl            :: (a -> b -> a) -> a -> [b] -> [a]
scanl f q xs     =  q : (case xs of
                            []   -> []
                            x:xs -> scanl f (f q x) xs
                        )

scanl1           :: (a -> a -> a) -> [a] -> [a]
scanl1 f (x:xs)  =  scanl f x xs
scanl1 _ []      =  []

foldr            :: (a -> b -> b) -> b -> [a] -> b
foldr f z []     =  z
foldr f z (x:xs) =  f x (foldr f z xs)


foldr1           :: (a -> a -> a) -> [a] -> a
foldr1 f [x]     =  x
foldr1 f (x:xs)  =  f x (foldr1 f xs)
foldr1 _ []      =  error "Prelude.foldr1: empty list"


{-
scanr             :: (a -> b -> b) -> b -> [a] -> [b]
scanr f q0 []     =  [q0]
scanr f q0 (x:xs) =  f x q : qs
                     where qs@(q:_) = scanr f q0 xs 


scanr1          :: (a -> a -> a) -> [a] -> [a]
scanr1 f []     =  []
scanr1 f [x]    =  [x]
scanr1 f (x:xs) =  f x q : qs
                   where qs@(q:_) = scanr1 f xs 
-}


iterate          :: (a -> a) -> a -> [a]
iterate f x      =  x : iterate f (f x)



repeat           :: a -> [a]
repeat x         =  xs where xs = x:xs


replicate        :: Integer -> a -> [a]
replicate n x    =  take n (repeat x)

cycle            :: [a] -> [a]
cycle []         =  error "Prelude.cycle: empty list"
cycle xs         =  xs' where xs' = append xs xs'

take                   :: Integer -> [a] -> [a]
-- take n _      | n <= 0 =  []
take _ []              =  []
take n (x:xs)          =  x : take (n-1) xs

drop                   :: Integer -> [a] -> [a]
-- drop n xs     | n <= 0 =  xs
drop _ []              =  []
drop n ((:) _ xs)          =  drop (n-1) xs


splitAt                  :: Integer -> [a] -> ([a],[a])
splitAt n xs             =  (take n xs, drop n xs)

takeWhile               :: (a -> Bool) -> [a] -> [a]
takeWhile p []          =  []
takeWhile p (x:xs) 
            | p x       =  x : takeWhile p xs
            | otherwise =  []


{-
dropWhile               :: (a -> Bool) -> [a] -> [a]
dropWhile p []          =  []
dropWhile p xs@(x:xs')
            | p x       =  dropWhile p xs'
            | otherwise =  xs

span                    :: (a -> Bool) -> [a] -> ([a],[a])
span p []               = ([],[])
span p xs@(x:xs') 
            | p x       =  (x:ys,zs) 
            | otherwise =  ([],xs)
                           where (ys,zs) = span p xs'

break                   :: (a -> Bool) -> [a] -> ([a],[a])
break p                 =  span (not . p)
-}

{-

-- lines breaks a string up into a list of strings at newline characters.
-- The resulting strings do not contain newlines.  Similary, words
-- breaks a string up into a list of words, which were delimited by
-- white space.  unlines and unwords are the inverse operations.
-- unlines joins lines with terminating newlines, and unwords joins
-- words with separating spaces.


lines            :: String -> [String]
lines ""         =  []
lines s          =  let (l, s') = break (== '\n') s
                      in  l : case s' of
                                []      -> []
                                (_:s'') -> lines s''


words            :: String -> [String]
words s          =  case dropWhile Char.isSpace s of
                      "" -> []
                      s' -> w : words s''
                            where (w, s'') = break Char.isSpace s'
-}

unlines          :: [[Char]] -> [Char]
unlines          =  concatMap (\ x -> append x "\n")



unwords          :: [[Char]] -> [Char]
unwords []       =  ""
unwords ws       =  foldr1 (\w s -> append w (' ':s)) ws

reverse          :: [a] -> [a]
reverse          =  foldl (flip (:)) []

and              :: [Bool] -> Bool
and              =  foldr amp True
or               =  foldr bar False

any              :: (a -> Bool) -> [a] -> Bool
any p            =  comp or (map p)
all p            =  comp and (map p)


{-
-- elem is the list membership predicate, usually written in infix form,
-- e.g., x `elem` xs.  notElem is the negation.

elem, notElem    :: (Eq a) => a -> [a] -> Bool
elem x           =  any (== x)
notElem x        =  all (/= x)

-- lookup key assocs looks up a key in an association list.

lookup           :: (Eq a) => a -> [(a,b)] -> Maybe b
lookup key []    =  Nothing
lookup key ((x,y):xys)
    | key == x   =  Just y
    | otherwise  =  lookup key xys
-}



sum     :: [Integer] -> Integer
sum              =  foldl (+) 0  
product          =  foldl (*) 1


maximum :: [Integer] -> Integer
maximum []       =  error "Prelude.maximum: empty list"
maximum xs       =  foldl1 max xs

minimum []       =  error "Prelude.minimum: empty list"
minimum xs       =  foldl1 min xs


zip              :: [a] -> [b] -> [(a,b)]
zip              =  zipWith (,)

{-
zip3             :: [a] -> [b] -> [c] -> [(a,b,c)]
zip3             =  zipWith3 (,,)
-}

zipWith          :: (a->b->c) -> [a]->[b]->[c]
zipWith z (a:as) (b:bs)
                 =  z a b : zipWith z as bs
zipWith _ _ _    =  []

zipWith3         :: (a->b->c->d) -> [a]->[b]->[c]->[d]
zipWith3 z (a:as) (b:bs) (c:cs)
                 =  z a b c : zipWith3 z as bs cs
zipWith3 _ _ _ _ =  []


{-
unzip            :: [(a,b)] -> ([a],[b])
unzip            =  foldr (\(a,b) ~(as,bs) -> (a:as,b:bs)) ([],[])

unzip3           :: [(a,b,c)] -> ([a],[b],[c])
unzip3           =  foldr (\(a,b,c) ~(as,bs,cs) -> (a:as,b:bs,c:cs))
                          ([],[],[])
-}