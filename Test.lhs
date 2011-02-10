> module Test where

> import Text.PrettyPrint.HughesPJ
> import qualified Text.ParserCombinators.Parsec.IndentParser as I

> import Parser
> import PrettyPrinter
> import Syntax
> import TypeCheck

> test f = mapM_ (putStrLn . f)


> roundTrip :: String -> String
> roundTrip s = case I.parse program "roundTrip" s of
>     Right prog  ->
>         let s' = show $ prettyHigh prog in
>         case I.parse program "roundTrip2" s' of
>             Right prog'
>               | prog == prog'  ->
>                 "PASS:\n" ++ show (prettyHigh prog')
>               | otherwise      ->
>                 "FAIL: round trip mismatch:\n" ++ s ++ "\n" ++ s'
>                     ++ "\n" ++ show (prettyHigh prog')
>                     ++ "\n" ++ show prog ++ "\n" ++ show prog'
>             Left err ->
>                 "FAIL: round trip re-parse:\n" ++ s' ++ "\n" ++ show err
>     Left err -> "FAIL: initial parse:\n" ++ s ++ "\n" ++ show err

> roundTripTest = test roundTrip roundTripTestData

> roundTripTestData = 
>   "f = x" :
>   "f = a b" :
>   "f = \\ x -> x" :
>   "f = \\ x y z -> a b c" :
>   "f = a\ng = b" :
>   "f = x (y z)" :
>   "f = a\n b" :
>   "f = x :: a" :
>   "f = x :: a -> b -> c" :
>   "f = x :: Foo" :
>   "f = x :: Foo a" :
>   "f = x :: (->)" :
>   "f = x :: (->) a b" :
>   "f = x :: F a -> G b" :
>   "f = \\ x -> x :: a -> b" :
>   "f = (\\ x -> x) :: a -> b" :
>   "f = x :: forall (a :: *) . a" :
>   "f = x :: forall a . a" :
>   "f = x :: forall a b c . a" :
>   "f = x :: forall (a :: Num)b(c :: * -> *)(d :: *) . a" :
>   "f = x :: forall a b . pi (c :: Num) d . b -> c" :
>   "f = x :: forall (a b c :: *) . a" :
>   "f x y z = x y z" :
>   "f Con = (\\ x -> x) :: (->) a a" :
>   "f Con = \\ x -> x :: (->) a" :
>   "f = f :: (forall a . a) -> (forall b. b)" : 
>   "f x y = (x y :: Nat -> Nat) y" :
>   "plus Zero n = n\nplus (Suc m) n = Suc (plus m n)" :
>   "data Nat where Zero :: Nat\n Suc :: Nat -> Nat" :
>   "data Foo :: (* -> *) -> (Num -> *) where Bar :: forall (f :: * -> *)(n :: Num) . (Vec (f Int) n -> a b) -> Foo f n" :
>   "data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). a -> Vec m a -> Vec (m+1) a" :
>   "huh = huh :: Vec (-1) a" :
>   "heh = heh :: Vec m a -> Vec n a -> Vec (m-n) a" :
>   "hah = hah :: Foo 0 1 (-1) (-2) m (m+n) (m+1-n+2)" :
>   "f :: a -> a\nf x = x" :
>   "f :: forall a. a -> a\nf x = x" :
>   "f :: forall a.\n a\n -> a\nf x = x" :
>   []



> parseCheck :: String -> String
> parseCheck s = case I.parse program "parseCheck" s of
>     Right p   -> case typeCheck p of
>         Right (p', (_, (), c)) -> "PASS: checked program\n"
>                                       ++ show (prettyProgram p')
>         Left err -> "FAIL: did not typecheck:\n" ++ s ++ "\n" ++ err
>     Left err  -> "FAIL: parse error:\n" ++ s ++ "\n" ++ show err



> parseCheckTest = test parseCheck parseCheckTestData

> parseCheckTestData = 
>   "f x = x" :
>   "f = f" :
>   "f = \\ x -> x" :
>   "f = (\\ x -> x) :: forall a. a -> a" :
>   "f x = x :: forall a b. a -> b" :
>   "f = \\ x y z -> x y z" :
>   "f x y z = x (y z)" :
>   "f x y z = x y z" :
>   "data Nat where\n Zero :: Nat\n Suc :: Nat -> Nat\nplus Zero n = n\nplus (Suc m) n = Suc (plus m n)\nf x = x :: Nat -> Nat" :
>   "data Nat where\n Zero :: Nat\n Suc :: Nat -> Nat\nf Suc = Suc" :
>   "data List :: * -> * where\n Nil :: forall a. List a\n Cons :: forall a. a -> List a -> List a\nsing = \\ x -> Cons x Nil\nsong x y = Cons x (Cons (sing y) Nil)\nappend Nil ys = ys\nappend (Cons x xs) ys = Cons x (append xs ys)" :
>   "data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). a -> Vec m a -> Vec (m+1) a\nhead (Cons x xs) = x\nid Nil = Nil\nid (Cons x xs) = Cons x xs\nid2 (Cons x xs) = Cons x xs\nid2 Nil = Nil\n" :
>   "f :: forall a b. (a -> b) -> (a -> b)\nf x = x" :
>   "f :: forall a. a\nf x = x" :
>   "f :: forall a. a -> a\nf x = x :: a" :
>   "f :: forall a. a -> (a -> a)\nf x y = y" :
>   "f :: (forall a. a) -> (forall b. b -> b)\nf x y = y" :
>   "f :: forall b. (forall a. a) -> (b -> b)\nf x y = y" :
>   "data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). a -> Vec m a -> Vec (m+1) a\nhead :: forall (n :: Num) a. Vec (1+n) a -> a\nhead (Cons x xs) = x\nid :: forall a (n :: Num). Vec n a -> Vec n a\nid Nil = Nil\nid (Cons x xs) = Cons x xs" :
>   "data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). a -> Vec m a -> Vec (m+1) a\nappend :: forall a (m n :: Num) . Vec m a -> Vec n a -> Vec (m+n) a\nappend Nil ys = ys\nappend (Cons x xs) ys = Cons x (append xs ys)" :
>   []
