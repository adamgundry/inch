> module Test where

> import Text.PrettyPrint.HughesPJ
> import qualified Text.ParserCombinators.Parsec.IndentParser as I

> import Parser
> import PrettyPrinter
> import Syntax
> import ProgramCheck

> test :: (a -> Either String String)
>             -> [a] -> Int -> Int -> String
> test f [] yes no = "Passed " ++ show yes ++ " tests, failed " ++ show no ++ " tests."
> test f (x:xs) yes no = case f x of
>     Right s  -> "PASS: " ++ s ++ "\n" ++ test f xs (yes+1) no
>     Left s   -> "FAIL: " ++ s ++ "\n" ++ test f xs yes (no+1)

> {-
> test :: (a -> Either String String)
>             -> [a] -> Int -> Int -> String
> test f xs yes no = let
>     (fails, passes) = partitionEithers (map f xs)
>     str a           = concatMap (\ s -> a ++ ": " ++ s ++ "\n")
>     in str "PASS" passes ++ "\n" ++ str "FAIL" fails ++
>      "\nPassed " ++ show (length passes) ++ " tests, failed "
>      ++ show (length fails) ++ " tests."
> -}

> runTest f xs yes no = putStrLn $ test f xs yes no


> roundTrip :: String -> Either String String
> roundTrip s = case I.parse program "roundTrip" s of
>     Right prog  ->
>         let s' = show $ vcatPretty prog in
>         case I.parse program "roundTrip2" s' of
>             Right prog'
>               | prog == prog'  -> Right $ show (vcatPretty prog')
>               | otherwise      -> Left $ "Round trip mismatch:"
>                     ++ "\n" ++ s ++ "\n" ++ s'
>                     ++ "\n" ++ show (vcatPretty prog')
>                     ++ "\n" ++ show prog ++ "\n" ++ show prog'
>             Left err -> Left $ "Round trip re-parse:\n"
>                                    ++ s' ++ "\n" ++ show err
>     Left err -> Left $ "Initial parse:\n" ++ s ++ "\n" ++ show err

> roundTripTest = runTest roundTrip roundTripTestData 0 0

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
>   "f :: forall m n. m <= n => Vec m\nf = f" :
>   "f :: forall m n. (m) <= (n) => Vec m\nf = f" :
>   "f :: forall m n. (m + 1) <= (2 + n) => Vec m\nf = f" :
>   "f :: forall m n. m <= n, m <= n => Vec m\nf = f" :
>   "f :: forall m n. m <= n, (m + 1) <= n => Vec m\nf = f" :
>   "f :: forall m n. 0 <= n, n <= 10 => Vec m\nf = f" :
>   "f :: forall m n. (m + (- 1)) <= n => Vec m\nf = f" :
>   "f :: forall m n. 0 <= -1 => Vec m\nf = f" :
>   "f :: forall m n. 0 <= -n => Vec m\nf = f" :
>   "f :: forall m n. m ~ n => Vec m\nf = f" :
>   "f :: forall m n. m ~ (n + n) => Vec m\nf = f" :
>   []



> parseCheck :: (String, Bool) -> Either String String
> parseCheck (s, b) = case I.parse program "parseCheck" s of
>     Right p   -> case typeCheck p of
>         Right (p', st)
>             | b      -> Right $ "Accepted good program:\n"
>                                     ++ show (prettyProgram p') ++ "\n"
>             | not b  -> Left $ "Accepted bad program:\n"
>                                     ++ show (prettyProgram p') ++ "\n"
>         Left err
>             | b      -> Left $ "Rejected good program:\n"
>                             ++ s ++ "\n" ++ show (prettyHigh err) ++ "\n"
>             | not b  -> Right $ "Rejected bad program:\n"
>                             ++ s ++ "\n" ++ show (prettyHigh err) ++ "\n"
>     Left err  -> Left $ "Parse error:\n" ++ s ++ "\n" ++ show err ++ "\n"



> parseCheckTest = runTest parseCheck parseCheckTestData 0 0

> parseCheckTestData = 
>   ("f x = x", True) :
>   ("f = f", True) :
>   ("f = \\ x -> x", True) :
>   ("f = (\\ x -> x) :: forall a. a -> a", True) :
>   ("f x = x :: forall a b. a -> b", True) :
>   ("f = \\ x y z -> x y z", True) :
>   ("f x y z = x (y z)", True) :
>   ("f x y z = x y z", True) :
>   ("f x = x :: Foo", False) :
>   ("f :: forall a. a -> a\nf x = x", True) :
>   ("f :: forall a. a\nf = f", True) :
>   ("f :: forall a b. (a -> b) -> (a -> b)\nf = \\ x -> x", True) :
>   ("f :: forall a b c. (a -> b -> c) -> a -> b -> c\nf = \\ x y z -> x y z", True) :
>   ("f :: forall a b c. (b -> c) -> (a -> b) -> a -> c\nf x y z = x (y z)", True) :
>   ("f :: forall a b c. (a -> b -> c) -> a -> b -> c\nf x y z = x y z", True) :
>   ("data Nat where\n Zero :: Nat\n Suc :: Nat -> Nat\nplus Zero n = n\nplus (Suc m) n = Suc (plus m n)\nf x = x :: Nat -> Nat", True) :
>   ("data Nat where\n Zero :: Nat\n Suc :: Nat -> Nat\nf Suc = Suc", False) :
>   ("data Nat where\n Zero :: Nat\n Suc :: Nat -> Nat\nf Zero = Zero\nf x = \\ y -> y", False) :
>   ("data List :: * -> * where\n Nil :: forall a. List a\n Cons :: forall a. a -> List a -> List a\nsing = \\ x -> Cons x Nil\nsong x y = Cons x (Cons (sing y) Nil)\nappend Nil ys = ys\nappend (Cons x xs) ys = Cons x (append xs ys)", True) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). a -> Vec m a -> Vec (m+1) a\nhead (Cons x xs) = x\nid Nil = Nil\nid (Cons x xs) = Cons x xs\nid2 (Cons x xs) = Cons x xs\nid2 Nil = Nil\n", True) :
>   ("f :: forall a b. (a -> b) -> (a -> b)\nf x = x", True) :
>   ("f :: forall a. a\nf x = x", False) :
>   ("f :: forall a. a -> a\nf x = x :: a", True) :
>   ("f :: forall a. a -> (a -> a)\nf x y = y", True) :
>   -- ("f :: (forall a. a) -> (forall b. b -> b)\nf x y = y", True) :
>   -- ("f :: forall b. (forall a. a) -> (b -> b)\nf x y = y", True) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). a -> Vec m a -> Vec (m+1) a\nhead :: forall (n :: Num) a. Vec (1+n) a -> a\nhead (Cons x xs) = x\nid Nil = Nil\nid (Cons x xs) = Cons x xs", True) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). a -> Vec m a -> Vec (m+1) a\nappend :: forall a (m n :: Num) . Vec m a -> Vec n a -> Vec (m+n) a\nappend Nil ys = ys\nappend (Cons x xs) ys = Cons x (append xs ys)", True) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a (n :: Num). n ~ 0 => Vec n a\n Cons :: forall a (m n :: Num). m <= 0, n ~ (m + 1) => a -> Vec m a -> Vec n a\nappend :: forall a (m n :: Num) . Vec m a -> Vec n a -> Vec (m+n) a\nappend Nil ys = ys\nappend (Cons x xs) ys = Cons x (append xs ys)", True) :
>   ("data One where A :: Two -> One\ndata Two where B :: One -> Two", True) :
>   ("data Foo where Foo :: Foo\ndata Bar where Bar :: Bar\nf Foo = Foo\nf Bar = Foo", False) :
>   ("data Foo where Foo :: Foo\ndata Bar where Bar :: Bar\nf :: Bar -> Bar\nf Foo = Foo\nf Bar = Foo", False) :
>   ("data One where One :: One\ndata Ex where Ex :: forall a. a -> (a -> One) -> Ex\nf (Ex s f) = f s", True) :
>   ("data One where One :: One\ndata Ex where Ex :: forall a. a -> Ex\nf (Ex a) = a", False) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). a -> Vec m a -> Vec (m+1) a\nvtail :: forall (n :: Num) a. Vec (n+1) a -> Vec n a\nvtail (Cons x xs) = xs", True) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). a -> Vec m a -> Vec (m+1) a\nlie :: forall a (n :: Num) . Vec n a\nlie = Nil", False) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). 0 <= m => a -> Vec m a -> Vec (m+1) a\nhead :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> a\nhead (Cons x xs) = x", True) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). 0 <= m => a -> Vec m a -> Vec (m+1) a\nsilly :: forall a (m :: Num). m <= -1 => Vec m a -> a\nsilly (Cons x xs) = x", True) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). 0 <= m => a -> Vec m a -> Vec (m+1) a\nsilly :: forall a (m :: Num). m <= -1 => Vec m a -> a\nsilly (Cons x xs) = x\nbad = silly (Cons Nil Nil)", False) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). 0 <= m => a -> Vec m a -> Vec (m+1) a\nhead :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> a\nhead (Cons x xs) = x\nwrong = head Nil", False) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). 0 <= m => a -> Vec m a -> Vec (m+1) a\nhead :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> a\nhead (Cons x xs) = x\nwrong :: forall a. a\nwrong = head Nil", False) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). 0 <= m => a -> Vec m a -> Vec (m+1) a\nhead :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> a\nhead (Cons x xs) = x\nright = head (Cons Nil Nil)", True) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). 0 <= m => a -> Vec m a -> Vec (m+1) a\ntail :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> Vec m a\ntail (Cons x xs) = xs\ntwotails :: forall a (m :: Num). 0 <= m, 0 <= (m+1) => Vec (m+2) a -> Vec m a \ntwotails xs = tail (tail xs)", True) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a. Vec 0 a\n Cons :: forall a (m :: Num). 0 <= m => a -> Vec m a -> Vec (m+1) a\nf :: forall a (n m :: Num). n ~ m => Vec n a -> Vec m a\nf x = x", True) :
>   ("f :: forall a (n :: Num) . n ~ n => a -> a\nf x = x", True) :
>   ("f :: forall a (n :: Num) . n ~ m => a -> a\nf x = x", False) :
>   ("data Vec :: Num -> * -> * where\n Nil :: forall a (n :: Num). n ~ 0 => Vec n a\n Cons :: forall a (m n :: Num). n ~ (m + 1) => a -> Vec m a -> Vec n a\nid :: forall a (n :: Num) . Vec n a -> Vec n a\nid Nil = Nil", True) :
>   []



> checkPrelude = do
>     s <- readFile "Prelude.nhs"
>     putStrLn $ test parseCheck [(s, True)] 0 0