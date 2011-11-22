{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables #-}

module InchPrelude where

import Prelude hiding (subtract, even, odd, gcd, lcm, (^), (^^),
                         fromIntegral, realToFrac, sequence,
                         sequence_, mapM, mapM_, (=<<), id, const,
                         (.), flip, ($), ($!), (&&), (||), not,
                         otherwise, maybe, either, curry, uncurry,
                         until, asTypeOf, error, undefined, map, (++),
                         filter, concat, concatMap, head, tail, last,
                         init, null, length, (!!), foldl, foldl1,
                         scanl, scanl1, foldr, foldr1, scanr, scanr1,
                         iterate, repeat, replicate, take, drop,
                         splitAt, takeWhile, dropWhile, span, break,
                         lines, words, unlines, unwords, reverse, and,
                         or, any, all, elem, notElem, lookup, sum,
                         product, maximum, minimum, zip, zipWith,
                         zipWith3, cycle, map, fst, snd)


{-
class  Eq' a  where  
    (==.) :: a -> a -> Bool  
    (/=.) :: a -> a -> Bool


class  (Eq' a) => Ord' a  where  
    compare'              :: a -> a -> Ordering  
    (<), (<=), (>=), (>)  :: a -> a -> Bool  
    max', min'            :: a -> a -> a  


class  Enum' a  where  
    succ', pred'      :: a -> a  
    toEnum'           :: Int -> a  
    fromEnum'         :: a -> Int  
    enumFrom'         :: a -> [a]             -- [n..]  
    enumFromThen'     :: a -> a -> [a]        -- [n,n'..]  
    enumFromTo'       :: a -> a -> [a]        -- [n..m]  
    enumFromThenTo'   :: a -> a -> a -> [a]   -- [n,n'..m]  
 

class  Bounded' a  where  
    minBound'         :: a  
    maxBound'         :: a

-- Numeric classes  
 
class  (Eq a, Show a) =>  Num' a  where  
    (+.), (-.), (*.)    :: a -> a -> a  
    negate'           :: a -> a  
    abs, signum      :: a -> a  
    fromInteger'      :: Integer -> a  

class  (Num a, Ord a) =>  Real' a  where  
    toRational'       ::  a -> Rational

class (Real a, Enum a) =>  Integral' a  where  
    quot', rem'        :: a -> a -> a  
    div', mod'         :: a -> a -> a  
    quotRem', divMod'  :: a -> a -> (a,a)  
    toInteger'        :: a -> Integer  
 
class (Num a) =>  Fractional' a  where  
    (/.)              :: a -> a -> a  
    recip'            :: a -> a  
    fromRational'     :: Rational -> a  
 
class (Fractional a) =>  Floating' a  where  
    pi'                  :: a  
    exp', log', sqrt'      :: a -> a  
    (**.), logBase'       :: a -> a -> a  
    sin', cos', tan'       :: a -> a  
    asin', acos', atan'    :: a -> a  
    sinh', cosh', tanh'    :: a -> a  
    asinh', acosh', atanh' :: a -> a  
 
class (Real a, Fractional a) =>  RealFrac' a  where  
    properFraction'   :: forall b . (Integral b) => a -> (b,a)  
    truncate', round'  :: forall b . (Integral b) => a -> b  
    ceiling', floor'   :: forall b . (Integral b) => a -> b  
 
class (RealFrac a, Floating a) =>  RealFloat' a  where  
    floatRadix'       :: a -> Integer  
    floatDigits'      :: a -> Int  
    floatRange'       :: a -> (Int,Int)  
    decodeFloat'      :: a -> (Integer,Int)  
    encodeFloat'      :: Integer -> Int -> a  
    exponent'         :: a -> Int  
    significand'      :: a -> a  
    scaleFloat'       :: Int -> a -> a  
    isNaN', isInfinite', isDenormalized', isNegativeZero', isIEEE'  
                     :: a -> Bool  
    atan2'            :: a -> a -> a  
-}
 

subtract         :: Num a => a -> a -> a
subtract         =  flip (-)

even, odd        :: (Eq a, Num a, Integral a) => a -> Bool
even n           =  (==) (rem n 2) 0
odd              =  (.) not even

gcd              :: (Num a, Integral a) => a -> a -> a
gcd 0 0          =  error "Prelude.gcd: gcd 0 0 is undefined"
gcd x y          =  gcd' (abs x) (abs y)
                    where gcd' x 0  =  x
                          gcd' x y  =  gcd' y (rem x y)

lcm              :: (Num a, Integral a) => a -> a -> a
lcm _ 0          =  0
lcm 0 _          =  0
lcm x y          =  abs ((quot x (gcd x y)) * y)

(^)              :: (Num a, Num b, Eq b, Ord b, Integral b) => a -> b -> a
(^) x 0              =  1
(^) x n | (>) n 0    =  f x (n-1) x
                    where 
                          f :: a -> b -> a -> a
                          f _ 0 y = y
                          f x n y = g x n  where
                                    g x n | even n  = g (x*x) (quot n 2)
                                          | otherwise = f x (n-1) (x*y)
_ ^ _            = error "Prelude.^: negative exponent"


(^^)             :: (Num a, Fractional a, Eq b, Ord b, Num b, Integral b) => a -> b -> a
(^^) x n           | (>=) n 0 = (^) x n
                   | otherwise = recip (x^(-n))

fromIntegral     :: (Integral a, Num b) => a -> b  
fromIntegral     =  (.) fromInteger toInteger

realToFrac     :: (Real a, Fractional b) => a -> b  
realToFrac      =  (.) fromRational toRational 


{-
class  Functor f  where  
    fmap              :: (a -> b) -> f a -> f b

class  Monad m  where  
    (>>=)  :: m a -> (a -> m b) -> m b  
    (>>)   :: m a -> m b -> m b  
    return :: a -> m a  
    fail   :: String -> m a  
-}

sequence       :: forall a (m :: * -> *) . Monad m => [m a] -> m [a]  
sequence       =  foldr mcons (return [])  
                    where mcons p q = (>>=) p (\x -> (>>=) q (\y -> return (x:y)))

sequence_      :: forall a (m :: * -> *) . Monad m => [m a] -> m ()  
sequence_      =  foldr (>>) (return ())

mapM             :: forall a b (m :: * -> *) . Monad m => (a -> m b) -> [a] -> m [b]  
mapM f as        =  sequence (map f as)

mapM_            :: forall a b (m :: * -> *) . Monad m => (a -> m b) -> [a] -> m ()  
mapM_ f as       =  sequence_ (map f as)

(=<<)            :: forall a b (m :: * -> *) . Monad m => (a -> m b) -> m a -> m b  
(=<<) f x          =  (>>=) x f

 
-- data  ()  =  ()  deriving (Eq, Ord, Enum, Bounded)  



id               :: a -> a
id x             =  x

const            :: a -> b -> a
const x _        =  x

(.)              :: (b -> c) -> (a -> b) -> a -> c
(.) f g          =  \ x -> f (g x)

flip             :: (a -> b -> c) -> b -> a -> c
flip f x y       =  f y x


($), ($!) :: (a -> b) -> a -> b
($) f  x    =  f x
($!) f x    =  seq x (f x)


-- built in
data  Bool' where
     False' :: Bool'
     True'  :: Bool'
   deriving (Eq, Ord, Enum, Read, Show, Bounded)

(&&), (||)      :: Bool -> Bool -> Bool
True  && x      =  x
False && _      =  False

True  || _      =  True
False || x      =  x
                                    

-- built in
not              :: Bool -> Bool
not True         =  False
not False        =  True

otherwise        :: Bool
otherwise        =  True



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


numericEnumFrom'         :: (Num a, Fractional a) => a -> [a]  
numericEnumFromThen'     :: (Num a, Fractional a) => a -> a -> [a]  
numericEnumFromTo'       :: (Num a, Fractional a, Ord a) => a -> a -> [a]  
numericEnumFromThenTo'   :: (Num a, Fractional a, Ord a) => a -> a -> a -> [a]  
numericEnumFrom'         =  iterate (\ x -> x+1)  
numericEnumFromThen' n m =  iterate (\ x -> x +(m-n)) n  
numericEnumFromTo' n m   =  takeWhile (\ x -> (<=) x ((/) (m+1) 2)) (numericEnumFrom' n)  
numericEnumFromThenTo' n n' m = takeWhile p (numericEnumFromThen' n n')  
                             where  
                               p | (>=) n' n   = (\ x -> (<=) x (m + ((/) (n'-n) 2)))  
                                 | otherwise = (\ x -> (>=) x (m + ((/) (n'-n) 2))) 



-- data  [a]  =  [] | a : [a]  deriving (Eq, Ord)
-- data  (a,b)   =  (a,b)    deriving (Eq, Ord, Bounded)

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

(++) :: [a] -> [a] -> [a]
[]     ++ ys = ys
(x:xs) ++ ys = x : (++) xs ys

filter :: (a -> Bool) -> [a] -> [a]
filter p []                 = []
filter p (x:xs) | p x       = x : filter p xs
                | otherwise = filter p xs

concat :: [[a]] -> [a]
concat xss = foldr (++) [] xss


concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f = (.) concat (map f)

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


(!!)                :: [a] -> Int -> a
(!!) xs     n | (<) n 0 =  error "Prelude.!!: negative index"
(!!) []     _         =  error "Prelude.!!: index too large"
(!!) (x:_)  0         =  x
(!!) (_:xs) n         =  (!!) xs (n-1)



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


scanr             :: (a -> b -> b) -> b -> [a] -> [b]
scanr f q0 []     =  [q0]
scanr f q0 (x:xs) =  f x q : qs
                     where qs = scanr f q0 xs 
                           q = head qs


scanr1          :: (a -> a -> a) -> [a] -> [a]
scanr1 f []     =  []
scanr1 f [x]    =  [x]
scanr1 f (x:xs) =  f x q : qs
                   where qs = scanr1 f xs 
                         q = head qs


iterate          :: (a -> a) -> a -> [a]
iterate f x      =  x : iterate f (f x)



repeat           :: a -> [a]
repeat x         =  xs where xs = x:xs


replicate        :: Integer -> a -> [a]
replicate n x    =  take n (repeat x)

cycle            :: [a] -> [a]
cycle []         =  error "Prelude.cycle: empty list"
cycle xs         =  xs' where xs' = (++) xs xs'

take                   :: Integer -> [a] -> [a]
take n _      | (<=) n 0 =  []
take _ []                =  []
take n (x:xs)            =  x : take (n-1) xs

drop                   :: Integer -> [a] -> [a]
drop n xs     | (<=) n 0 =  xs
drop _ []                =  []
drop n ((:) _ xs)        =  drop (n-1) xs


splitAt                  :: Integer -> [a] -> ([a],[a])
splitAt n xs             =  (take n xs, drop n xs)

takeWhile               :: (a -> Bool) -> [a] -> [a]
takeWhile p []          =  []
takeWhile p (x:xs) 
            | p x       =  x : takeWhile p xs
            | otherwise =  []


dropWhile               :: (a -> Bool) -> [a] -> [a]
dropWhile p []          =  []
dropWhile p xs
            | p (head xs)  =  dropWhile p (tail xs)
            | otherwise    =  xs

span                    :: (a -> Bool) -> [a] -> ([a],[a])
span p []               = ([],[])
span p xs
            | p (head xs) =  (x:fst yszs, snd yszs) 
            | otherwise   =  ([],xs)
                           where yszs = span p (tail xs)
                                 x = head xs

break                   :: (a -> Bool) -> [a] -> ([a],[a])
break p                 =  span ((.) not p)





lines            :: [Char] -> [[Char]]
lines ""         =  []
lines s          =  let ls' = break ((==) '\n') s
                        l = fst ls'
                        s' = snd ls'
                      in  l : (case s' of
                                []      -> []
                                (_:s'') -> lines s''
                              )


words            :: [Char] -> [[Char]]
words s          =  case dropWhile isSpace s of
                      "" -> []
                      s' -> w : words s''
                            where ws'' = break isSpace s'
                                  w = fst ws''
                                  s'' = snd ws''
  where
    isSpace ' '  = True
    isSpace _    = False

unlines          :: [[Char]] -> [Char]
unlines          =  concatMap (\ x -> (++) x "\n")



unwords          :: [[Char]] -> [Char]
unwords []       =  ""
unwords ws       =  foldr1 (\w s -> (++) w (' ':s)) ws

reverse          :: [a] -> [a]
reverse          =  foldl (flip (:)) []

and              :: [Bool] -> Bool
and              =  foldr (&&) True
or               =  foldr (||) False

any              :: (a -> Bool) -> [a] -> Bool
any p            =  (.) or (map p)
all p            =  (.) and (map p)


elem, notElem    :: (Eq a) => a -> [a] -> Bool
elem x           =  any ((==) x)
notElem x        =  all ((/=) x)

lookup           :: (Eq a) => a -> [(a,b)] -> Maybe b
lookup key []    =  Nothing
lookup key ((x,y):xys)
    | (==) key x   =  Just y
    | otherwise    =  lookup key xys



sum     :: Num a => [a] -> a
sum              =  foldl (+) 0  
product          =  foldl (*) 1


maximum :: Ord a => [a] -> a
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