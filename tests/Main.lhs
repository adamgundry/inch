> module Main where

> import Control.Applicative
> import Control.Monad.State
> import Data.List
> import System.Directory

> import Language.Inch.Syntax
> import Language.Inch.Parser
> import Language.Inch.PrettyPrinter
> import Language.Inch.ProgramCheck
> import Language.Inch.Erase

> main :: IO ()
> main = checks "examples/"


> test :: (a -> String) -> (a -> Either String String)
>             -> [a] -> Int -> Int -> String
> test _ _ [] yes no = "Passed " ++ show yes ++ " tests, failed "
>                          ++ show no ++ " tests."
> test g f (x:xs) yes no = "TEST\n" ++ g x ++ "\n" ++ case f x of
>     Right s  -> "PASS\n" ++ s ++ "\n" ++ test g f xs (yes+1) no
>     Left s   -> "FAIL\n" ++ s ++ "\n" ++ test g f xs yes (no+1)

> runTest :: (a -> String) -> (a -> Either String String) -> [a] -> Int -> Int -> IO ()
> runTest g f xs yes no = putStrLn $ test g f xs yes no


> roundTripTest, parseCheckTest, eraseCheckTest :: IO ()
> roundTripTest  = runTest id roundTrip roundTripTestData 0 0
> parseCheckTest = runTest fst parseCheck parseCheckTestData 0 0
> eraseCheckTest = runTest id eraseCheck (map fst . filter snd $ parseCheckTestData) 0 0

> roundTrip :: String -> Either String String
> roundTrip s = case parseProgram "roundTrip" s of
>     Right (prog, _)  ->
>         let s' = show $ vcatPretty prog in
>         case parseProgram "roundTrip2" s' of
>             Right (prog', _)
>               | prog == prog'  -> Right $ show (vcatPretty prog')
>               | otherwise      -> Left $ "Round trip mismatch:"
>                     ++ "\n" ++ s ++ "\n" ++ s'
>                     ++ "\n" ++ show (vcatPretty prog')
>                     -- ++ "\n" ++ show prog ++ "\n" ++ show prog'
>             Left err -> Left $ "Round trip re-parse:\n"
>                                    ++ s' ++ "\n" ++ show err
>     Left err -> Left $ "Initial parse:\n" ++ s ++ "\n" ++ show err

> parseCheck :: (String, Bool) -> Either String String
> parseCheck (s, b) = case parseProgram "parseCheck" s of
>     Right (p, _)   -> case runCheckProg p of
>         Right (p', _)
>             | b          -> Right $ "Accepted good program:\n"
>                                     ++ show (prettyProgram p') ++ "\n"
>             | otherwise  -> Left $ "Accepted bad program:\n"
>                                     ++ show (prettyProgram p') ++ "\n"
>         Left err
>             | b          -> Left $ "Rejected good program:\n"
>                             ++ show (prettySProgram p) ++ "\n" ++ renderMe err ++ "\n"
>             | otherwise  -> Right $ "Rejected bad program:\n"
>                             ++ show (prettySProgram p) ++ "\n" ++ renderMe err ++ "\n"
>     Left err  -> Left $ "Parse error:\n" ++ s ++ "\n" ++ show err ++ "\n"

> eraseCheck :: String -> Either String String
> eraseCheck s = case parseProgram "eraseCheck" s of
>     Right (p, _)   -> case runCheckProg p of
>         Right (p', st) -> case runStateT (eraseProg p') st of
>             Right (p'', _) -> case runCheckProg (map fog p'') of
>                 Right (p''', _) -> Right $ "Erased program:\n" ++ show (prettyProgram p''')
>                 Left err -> Left $ "Erased program failed to type check: " ++ renderMe err
>             Left err        -> Left $ "Erase error:\n" ++ s ++ "\n" ++ renderMe err ++ "\n"

>         Left err -> Right $ "Skipping rejected program:\n"
>                             ++ s ++ "\n" ++ renderMe err ++ "\n"
>     Left err  -> Left $ "Parse error:\n" ++ s ++ "\n" ++ show err ++ "\n"


> check :: FilePath -> IO ()
> check fn = do
>     s <- readFile fn
>     putStrLn $ test (const fn) parseCheck [(s, True)] 0 0

> checkEx :: IO ()
> checkEx = check "Example.hs"

> checks :: FilePath -> IO ()
> checks d = do
>     fns <- filter goodFile <$> getDirectoryContents d
>     fcs <- zip fns <$> mapM (readFile . (d ++)) fns
>     putStrLn $ test fst (\ (_, c) -> parseCheck (c, True)) fcs 0 0
>   where
>     goodFile fn = (".hs" `isSuffixOf` fn) && not ("Extras.hs" `isSuffixOf` fn)

> erase :: FilePath -> IO ()
> erase fn = do
>     s <- readFile fn
>     putStrLn $ test (const fn) eraseCheck [s] 0 0

> eraseEx :: IO ()
> eraseEx = erase "Example.hs"


> roundTripTestData :: [String]
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
>   "f :: pi (m :: Num) . Int\nf {0} = Zero\nf {n+1} = Suc f {n}" :
>   "f x _ = x" :
>   "f :: forall a. pi (m :: Num) . a -> Vec a\nf {0} a = VNil\nf {n} a = VCons a (f {n-1} a)" :
>   "x = 0" :
>   "x = plus 0 1" :
>   "x = let a = 1\n in a" :
>   "x = let a = \\ x -> f x y\n in let b = 2\n  in a" :
>   "x = let y :: forall a. a -> a\n        y = \\ z -> z\n        f = f\n  in y" :
>   "f :: 0 <= 1 => Integer\nf = 1" :
>   "f :: forall (m n :: Num) . (m <= n => Integer) -> Integer\nf = f" :
>   "f :: 0 + m <= n + 1 => Integer\nf = f" :
>   "f :: 0 < 1 => a\nf = f" :
>   "f :: 0 > 1 => a\nf = f" :
>   "f :: 1 >= 0, a + 3 > 7 => a\nf = f" :
>   "f x | gr x 0 = x" :
>   "f x | {x > 0} = x" :
>   "f x | {x > 0, x ~ 0} = x" :
>   "f x | {x >= 0} = x\n    | {x <  0} = negate x" :
>   "f :: forall (m :: Nat) . g m\nf = f" :
>   "f = \\ {x} -> x" :
>   "f = \\ {x} y {z} -> plus x y" :
>   "x = case True of  False -> undefined\n                  True -> 3" :
>   "x = case True of\n      False -> undefined\n      True -> 3" :
>   "x = case f 1 3 of\n    (Baz boo) -> boo boo" :
>   "x = case f 1 3 of\n     (Baz boo) -> boo boo\n     (Bif bof) -> bah" :
>   "x = case f 1 3 of\n    (Baz boo) | {2 ~ 3} -> boo boo" :
>   "x = case f 1 3 of\n     Baz boo | womble -> boo boo" :
>   "x = case f 1 3 of\n     Baz boo | {2 ~ 3} -> boo boo" :
>   "x = case a of\n  Wim -> Wam\n          Wom " :
>   "f :: g (abs (-6))\nf = f" :
>   "f :: g (signum (a + b))\nf = f" :
>   "f :: g (a ^ b + 3 ^ 2)\nf = f" :
>   "x = 2 + 3" :
>   "x = 2 - 3" :
>   "x = - 3" :
>   "f :: f ((*) 3 2) -> g (+)\nf = undefined" :
>   "x :: f min\nx = x" :
>   "data Foo where X :: Foo\n  deriving Show" :
>   "data Foo where\n    X :: Foo\n  deriving (Eq, Show)" :
>   "x :: [a]\nx = []" :
>   "y :: [Integer]\ny = 1 : 2 : [3, 4]" :
>   "x :: ()\nx = ()" :
>   "x :: (Integer, Integer)\nx = (3, 4)" :
>   "f () = ()\ng (x, y) = (y, x)" : 
>   "f [] = []\nf (x:y:xs) = x : xs" :
>   "f (_, x:_) = x" : 
>   "f [x,_] = x" : 
>   "x = a b : c d : e f" :
>   "f :: g (2 - 3)" :
>   "f xs = case xs of\n      [] -> []\n      y:ys -> ys" :
>   "a = \"hello\"" :
>   "b = 'w' : 'o' : 'r' : ['l', 'd']" :
>   "f (_:x) = x" :
>   []



> vecDecl, vec2Decl, vec3Decl, natDecl :: String

> vecDecl = "data Vec :: Num -> * -> * where\n"
>   ++ "  Nil :: forall a (n :: Num). n ~ 0 => Vec n a\n"
>   ++ "  Cons :: forall a (m n :: Num). 0 <= m, n ~ (m + 1) => a -> Vec m a -> Vec n a\n"
>   ++ " deriving (Eq, Show)\n"

> vec2Decl = "data Vec :: * -> Num -> * where\n"
>   ++ "  Nil :: forall a (n :: Num). n ~ 0 => Vec a n\n"
>   ++ "  Cons :: forall a (n :: Num). 1 <= n => a -> Vec a (n-1) -> Vec a n\n"

> vec3Decl = "data Vec :: Num -> * -> * where\n"
>   ++ "  Nil :: forall a . Vec 0 a\n"
>   ++ "  Cons :: forall a (n :: Num). 0 <= n => a -> Vec n a -> Vec (n+1) a\n"

> natDecl = "data Nat where\n Zero :: Nat\n Suc :: Nat -> Nat\n"

> parseCheckTestData :: [(String, Bool)]
> parseCheckTestData = 
>   ("f x = x", True) :
>   ("f = f", True) :
>   ("f = \\ x -> x", True) :
>   ("f = (\\ x -> x) :: forall a. a -> a", True) :
>   ("f x = x :: forall a b. a -> b", False) :
>   ("f = \\ x y z -> x y z", True) :
>   ("f x y z = x (y z)", True) :
>   ("f x y z = x y z", True) :
>   ("f x = x :: Foo", False) :
>   ("f :: a -> a\nf x = x", True) :
>   ("f :: a\nf = f", True) :
>   ("f :: forall a b. (a -> b) -> (a -> b)\nf = \\ x -> x", True) :
>   ("f :: (a -> b -> c) -> a -> b -> c\nf = \\ x y z -> x y z", True) :
>   ("f :: forall a b c. (b -> c) -> (a -> b) -> a -> c\nf x y z = x (y z)", True) :
>   ("f :: forall a b c. (a -> b -> c) -> a -> b -> c\nf x y z = x y z", True) :
>   (natDecl ++ "plus Zero n = n\nplus (Suc m) n = Suc (plus m n)\nf x = x :: Nat -> Nat", True) :
>   (natDecl ++ "f Suc = Suc", False) :
>   (natDecl ++ "f Zero = Zero\nf x = \\ y -> y", False) :
>   ("data List :: * -> * where\n Nil :: forall a. List a\n Cons :: forall a. a -> List a -> List a\nsing = \\ x -> Cons x Nil\nsong x y = Cons x (Cons (sing y) Nil)\nappend Nil ys = ys\nappend (Cons x xs) ys = Cons x (append xs ys)", True) :
>   ("f :: forall a b. (a -> b) -> (a -> b)\nf x = x", True) :
>   ("f :: forall a. a\nf x = x", False) :
>   ("f :: forall a. a -> a\nf x = x :: a", True) :
>   ("f :: forall a. a -> (a -> a)\nf x y = y", True) :
>   ("f :: (forall a. a) -> (forall b. b -> b)\nf x y = y", True) :
>   ("f :: forall b. (forall a. a) -> (b -> b)\nf x y = y", True) :
>   ("data One where A :: Two -> One\ndata Two where B :: One -> Two", True) :
>   ("data Foo where Foo :: Foo\ndata Bar where Bar :: Bar\nf Foo = Foo\nf Bar = Foo", False) :
>   ("data Foo where Foo :: Foo\ndata Bar where Bar :: Bar\nf :: Bar -> Bar\nf Foo = Foo\nf Bar = Foo", False) :
>   ("f :: forall a (n :: Num) . n ~ n => a -> a\nf x = x", True) :
>   ("f :: forall a (n :: Num) . n ~ m => a -> a\nf x = x", False) :
>   (vecDecl ++ "head (Cons x xs) = x\nid2 Nil = Nil\nid2 (Cons x xs) = Cons x xs", False) :
>   (vecDecl ++ "head :: forall (n :: Num) a. Vec (1+n) a -> a\nhead (Cons x xs) = x\nid2 :: forall (n :: Num) a. Vec n a -> Vec n a\nid2 Nil = Nil\nid2 (Cons x xs) = Cons x xs", True) :
>   (vecDecl ++ "append :: forall a (m n :: Num) . 0 <= m, 0 <= n, 0 <= (m + n) => Vec m a -> Vec n a -> Vec (m+n) a\nappend Nil ys = ys\nappend (Cons x xs) ys = Cons x (append xs ys)", True) :
>   (vecDecl ++ "append :: forall a (m n :: Num) . 0 <= n => Vec m a -> Vec n a -> Vec (m+n) a\nappend Nil ys = ys\nappend (Cons x xs) ys = Cons x (append xs ys)", True) :
>   (vecDecl ++ "tail :: forall (n :: Num) a. Vec (n+1) a -> Vec n a\ntail (Cons x xs) = xs", True) :
>   (vecDecl ++ "lie :: forall a (n :: Num) . Vec n a\nlie = Nil", False) :
>   (vecDecl ++ "head :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> a\nhead (Cons x xs) = x", True) :
>   (vecDecl ++ "silly :: forall a (m :: Num). m <= -1 => Vec m a -> a\nsilly (Cons x xs) = x", True) :
>   (vecDecl ++ "silly :: forall a (m :: Num). m <= -1 => Vec m a -> a\nsilly (Cons x xs) = x\nbad = silly (Cons Nil Nil)", False) :
>   (vecDecl ++ "head :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> a\nhead (Cons x xs) = x\nwrong = head Nil", False) :
>   (vecDecl ++ "head :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> a\nhead (Cons x xs) = x\nright = head (Cons Nil Nil)", True) :
>   (vecDecl ++ "tail :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> Vec m a\ntail (Cons x xs) = xs\ntwotails :: forall a (m :: Num). 0 <= m, 0 <= (m+1) => Vec (m+2) a -> Vec m a \ntwotails xs = tail (tail xs)", True) :
>   (vecDecl ++ "tail :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> Vec m a\ntail (Cons x xs) = xs\ntwotails xs = tail (tail xs)", True) :
>   (vecDecl ++ "f :: forall a (n m :: Num). n ~ m => Vec n a -> Vec m a\nf x = x", True) :
>   (vecDecl ++ "id2 :: forall a (n :: Num) . Vec n a -> Vec n a\nid2 Nil = Nil\nid2 (Cons x xs) = Cons x xs", True) :
>   (vecDecl ++ "id2 :: forall a (n m :: Num) . Vec n a -> Vec m a\nid2 Nil = Nil\nid2 (Cons x xs) = Cons x xs", False) :
>   (vecDecl ++ "id2 :: forall a (n m :: Num) . n ~ m => Vec n a -> Vec m a\nid2 Nil = Nil\nid2 (Cons x xs) = Cons x xs", True) :
>   (vec2Decl ++ "id2 :: forall a (n m :: Num) . n ~ m => Vec a n -> Vec a m\nid2 Nil = Nil\nid2 (Cons x xs) = Cons x xs", True) :
>   ("f :: forall a. 0 ~ 1 => a\nf = f", False) :
>   -- ("x = y\ny = x", True) :
>   ("f :: forall a . pi (m :: Num) . a -> a\nf {0} x = x\nf {n} x = x", True) :
>   ("f :: forall a . a -> (pi (m :: Num) . a)\nf x {m} = x", True) :
>   (vecDecl ++ "vec :: forall a . pi (m :: Num) . 0 <= m => a -> Vec m a\nvec {0} x = Nil\nvec {n+1} x = Cons x (vec {n} x)", True) :
>   (natDecl ++ "nat :: pi (n :: Num) . 0 <= n => Nat\nnat {0} = Zero\nnat{m+1} = Suc (nat {m})", True) :
>   -- ("data T :: Num -> * where C :: pi (n :: Num) . T n\nf (C {j}) = C {j}", True) :
>   -- ("data T :: Num -> * where C :: pi (n :: Num) . T n\nf :: forall (n :: Num) . T n -> T n\nf (C {i}) = C {i}", True) :
>   ("data T :: Num -> * where C :: forall (m :: Num) . pi (n :: Num) . m ~ n => T m\nf :: forall (n :: Num) . T n -> T n\nf (C {i}) = C {i}", True) :
>   -- ("data T :: Num -> * where C :: pi (n :: Num) . T n\nf :: forall (n :: Num) . T n -> T n\nf (C {0}) = C {0}\nf (C {n+1}) = C {n+1}", True) :
>   ("data T :: Num -> * where C :: forall (m :: Num) . pi (n :: Num) . m ~ n => T m\nf :: forall (n :: Num) . T n -> T n\nf (C {0}) = C {0}\nf (C {n+1}) = C {n+1}", True) :
>   ("f :: Integer -> Integer\nf x = x", True) :
>   ("f :: pi (n :: Num) . Integer\nf {n} = n", True) :
>   ("f :: pi (n :: Num) . Integer\nf {0} = 0\nf {n+1} = n", True) :
>   ("f :: pi (n :: Num) . Integer\nf {n+1} = n", True) :
>   (vecDecl ++ "vtake :: forall (n :: Num) a . pi (m :: Num) . 0 <= m, 0 <= n => Vec (m + n) a -> Vec m a\nvtake {0}   _            = Nil\nvtake {i+1} (Cons x xs) = Cons x (vtake {i} xs)", True) :
>   (vecDecl ++ "vfold :: forall (n :: Num) a (f :: Num -> *) . f 0 -> (forall (m :: Num) . 0 <= m => a -> f m -> f (m + 1)) -> Vec n a -> f n\nvfold n c Nil         = n\nvfold n c (Cons x xs) = c x (vfold n c xs)", True) :
>   ("data One where One :: One\ndata Ex where Ex :: forall a. a -> (a -> One) -> Ex\nf (Ex s g) = g s", True) :
>   ("data One where One :: One\ndata Ex where Ex :: forall a. a -> (a -> One) -> Ex\nf :: Ex -> One\nf (Ex s g) = g s", True) :
>   ("data One where One :: One\ndata Ex where Ex :: forall a. a -> Ex\nf (Ex a) = a", False) :
>   ("data One where One :: One\ndata Ex where Ex :: forall a. a -> Ex\nf (Ex One) = One", False) :
>   ("data Ex where Ex :: pi (n :: Num) . Ex\nf (Ex {n}) = n", True) : 
>   ("data Ex where Ex :: pi (n :: Num) . Ex\ndata T :: Num -> * where T :: pi (n :: Num) . T n\nf (Ex {n}) = T {n}", False) :
>   ("data Ex where Ex :: pi (n :: Num) . Ex\ndata T :: Num -> * where T :: pi (n :: Num) . T n\nf (Ex {n+1}) = T {n}", False) : 
>   ("f = let g = \\ x -> x\n in g g", True) :
>   ("f = let x = x\n in x", True) :
>   ("f = let x = 0\n in x", True) :
>   ("f = let x = 0\n in f", True) :
>   ("f = let g x y = y\n in g f", True) :
>   ("f x = let y = x\n in y", True) :
>   ("f x = let y z = x\n          a = a\n  in y (x a)", True) :
>   ("f :: forall a. a -> a\nf x = x :: a", True) :
>   ("f :: forall b. (forall a. a -> a) -> b -> b\nf c = c\ng = f (\\ x -> x)", True) :
>   ("f :: forall b. (forall a. a -> a) -> b -> b\nf c = c\ng = f (\\ x y -> x)", False) :
>   ("f :: forall b. (forall a. a -> a) -> b -> b\nf c = c c\ng = f (\\ x -> x) (\\ x y -> y)", True) :
>   ("f :: forall b. (forall a. a -> a -> a) -> b -> b\nf c x = c x x\ng = f (\\ x y -> x)", True) :
>   (vec2Decl ++ "vfold :: forall (n :: Num) a (f :: Num -> *) . f 0 -> (forall (m :: Num) . 1 <= m => a -> f (m-1) -> f m) -> Vec a n -> f n\nvfold = vfold\nvbuild :: forall (n :: Num) a . Vec a n -> Vec a n\nvbuild = vfold Nil Cons", True) :
>   (vec2Decl ++ "vfold :: forall (n :: Num) a (f :: Num -> *) . f 0 -> (forall (m :: Num) . 1 <= m => a -> f (m-1) -> f m) -> Vec a n -> f n\nvfold = vfold\nvbuild = vfold Nil Cons", True) :
>   ("f :: forall b. (forall a . pi (m :: Num) . 0 <= m => a -> a) -> b -> b\nf h = h {0}\ng :: forall a . pi (m :: Num) . a -> a\ng {m} = \\ x -> x\ny = f g", True) :
>   ("f :: forall b. (forall a . pi (m :: Num) . 0 <= m, m <= 3 => a -> a) -> b -> b\nf h = h {0}\ng :: forall a . pi (m :: Num) . 0 <= m, m <= 3 => a -> a\ng {m} = \\ x -> x\ny = f g", True) :
>   ("f :: forall b. (forall a . pi (m :: Num) . 0 <= m, m <= 3 => a -> a) -> b -> b\nf h = h {0}\ng :: forall a . pi (m :: Num) . m <= 3, 0 <= m => a -> a\ng {m} = \\ x -> x\ny = f g", True) :
>   ("f :: forall (b :: Num -> *) (n :: Num) . 0 <= n, n <= 3 => (forall (a :: Num -> *) (m :: Num) . 0 <= m, m <= 3 => a m -> a m) -> b n -> b n\nf h = h\ng :: forall (a :: Num -> *) (m :: Num) . m <= 3, 0 <= m => a m -> a m\ng = \\ x -> x\ny = f g", True) :
>   ("f :: ((Integer -> (forall a. a -> a)) -> Integer) -> (Integer -> (forall a . a)) -> Integer\nf g h = g h", True) : 
>   ("f :: ((Integer -> (forall a. a -> a)) -> Integer) -> (Integer -> (forall a . a)) -> Integer\nf = f", True) : 
>   ("f :: (Integer -> (forall a. a -> a)) -> (forall b . (b -> b) -> (b -> b))\nf x = x 0", True) :
>   ("f :: (Integer -> Integer -> (pi (m :: Num) . forall a. a -> a)) -> Integer -> (pi (m :: Num) . forall d b . (b -> b) -> (b -> b))\nf x = x 0", True) :
>   ("f :: (forall a. a) -> (forall a. a) -> (forall a.a)\nf x y = x\ng = let loop = loop\n    in f loop", True) :
>   ("f :: (forall a. a) -> (forall a. a) -> (forall a.a)\nf x y = x\ng = let loop = loop\n    in f loop\nh :: Integer\nh = g 0", False) :
>   ("loop :: forall a. a\nloop = loop\nf :: (forall a. a) -> (forall a. a) -> (forall a.a)\nf x y = x\ng = f loop\nh :: Integer\nh = g 0", False) :
>   ("f :: (forall a. a) -> (forall a. a) -> (forall a.a)\nf x y = x\ng :: (forall x . x) -> (forall y. y -> y)\ng = let loop = loop\n    in f loop", True) :
>   ("f :: (forall a. a) -> (forall a. a) -> (forall a.a)\nf x y = x\ng :: (forall x . x -> x) -> (forall y. y)\ng = let loop = loop\n    in f loop", False) :
>   ("data High where High :: (forall a. a) -> High\nf (High x) = x", True) :
>   ("data Higher where Higher :: ((forall a. a) -> Integer) -> Higher\nf (Higher x) = x", True) :
>   ("data Higher where Higher :: ((forall a. a) -> Integer) -> Higher\nf :: Higher -> (forall a. a) -> Integer\nf (Higher x) = x", True) :
>   ("data Higher where Higher :: ((forall a. a) -> Integer) -> Higher\nf (Higher x) = x\nx = f (Higher (\\ zzz -> 0)) 0", False) :
>   ("tri :: forall a . pi (m n :: Num) . (m < n => a) -> (m ~ n => a) -> (m > n => a) -> a\ntri = tri\nf :: pi (m n :: Num) . m ~ n => Integer\nf = f\nloop = loop\ng :: pi (m n :: Num) . Integer\ng {m} {n} = tri {m} {n} loop (f {m} {n}) loop", True) :
>   ("tri :: forall a . pi (m n :: Num) . (m < n => a) -> (m ~ n => a) -> (m > n => a) -> a\ntri = undefined\ntri2 :: forall a . pi (m n :: Num) . (m < n => a) -> (m ~ n => a) -> (m > n => a) -> a\ntri2 = tri", True) :
>   ("tri :: forall a . pi (m n :: Num) . (m < n => a) -> (m ~ n => a) -> (m > n => a) -> a\ntri = tri\nf :: pi (m n :: Num) . m ~ n => Integer\nf = f\nloop = loop\ng :: pi (m n :: Num) . Integer\ng {m} {n} = tri {m} {n} loop loop (f {m} {n})", False) :
>   ("f :: forall a. pi (m n :: Num) . m ~ n => a\nf = f\nid2 x = x\ny :: forall a . pi (m n :: Num) . a\ny {m} {n} = id2 (f {m} {n})", False) :
>   ("data Eq :: Num -> Num -> * where Refl :: forall (m n :: Num) . m ~ n => Eq m n\ndata Ex :: (Num -> *) -> * where Ex :: forall (p :: Num -> *)(n :: Num) . p n -> Ex p\nf :: pi (n :: Num) . Ex (Eq n)\nf {0} = Ex Refl\nf {n+1} = Ex Refl", True) :
>   ("data Eq :: Num -> Num -> * where Refl :: forall (m n :: Num) . m ~ n => Eq m n\ndata Ex :: (Num -> *) -> * where Ex :: forall (p :: Num -> *)(n :: Num) . p n -> Ex p\nf :: pi (n :: Num) . Ex (Eq n)\nf {0} = Ex Refl\nf {n+1} = f {n}", False) :
>   ("data Eq :: Num -> Num -> * where Refl :: forall (m n :: Num) . m ~ n => Eq m n\ndata Ex :: (Num -> *) -> * where Ex :: forall (p :: Num -> *) . pi (n :: Num) . p n -> Ex p\nf :: pi (n :: Num) . Ex (Eq n)\nf {0} = Ex {0} Refl\nf {n+1} = Ex {n+1} Refl", True) :
>   ("data Eq :: Num -> Num -> * where Refl :: forall (m n :: Num) . m ~ n => Eq m n\ndata Ex :: (Num -> *) -> * where Ex :: forall (p :: Num -> *) . pi (n :: Num) . p n -> Ex p\nf :: pi (n :: Num) . Ex (Eq n)\nf {0} = Ex {0} Refl\nf {n+1} = Ex {n} Refl", False) :
>   ("data Eq :: Num -> Num -> * where Refl :: forall (m n :: Num) . m ~ n => Eq m n\ndata Ex :: (Num -> *) -> * where Ex :: forall (p :: Num -> *) . pi (n :: Num) . p n -> Ex p\nf :: pi (n :: Num) . Ex (Eq n)\nf {0} = Ex {0} Refl\nf {n+1} = f {n}", False) :
>   ("data Eq :: Num -> Num -> * where Refl :: forall (m n :: Num) . m ~ n => Eq m n\ndata Ex :: (Num -> *) -> * where Ex :: forall (p :: Num -> *) . pi (n :: Num) . p n -> Ex p\nf :: pi (n :: Num) . Ex (Eq n)\nf {0} = Ex {0} Refl\nf {n+1} = f {n-1}", False) :
>   ("tri :: forall (a :: Num -> Num -> *) . (forall (m n :: Num) . 0 <= m, m < n => a m n) -> (forall (m   :: Num) . 0 <= m        => a m m) -> (forall (m n :: Num) . 0 <= n, n < m => a m n) -> (pi (m n :: Num) . 0 <= m, 0 <= n => a m n)\ntri a b c {0}   {n+1} = a\ntri a b c {0}   {0}   = b\ntri a b c {m+1} {0}   = c\ntri a b c {m+1} {n+1} = tri a b c {m} {n}", False) :
>   ("tri :: forall (a :: Num -> Num -> *) . (forall (m n :: Num) . 0 <= m, m < n => a m n) -> (forall (m   :: Num) . 0 <= m        => a m m) -> (forall (m n :: Num) . 0 <= n, n < m => a m n) -> (forall (m n :: Num) . 0 <= m, 0 <= n => a m n -> a (m+1) (n+1)) -> (pi (m n :: Num) . 0 <= m, 0 <= n => a m n)\ntri a b c step {0}   {n+1} = a\ntri a b c step {0}   {0}   = b\ntri a b c step {m+1} {0}   = c\ntri a b c step {m+1} {n+1} = step (tri a b c step {m} {n})", True) :
>   ("tri :: forall a . pi (m n :: Num) . 0 <= m, 0 <= n => (pi (d :: Num) . 0 < d, d ~ m - n => a) -> (n ~ m => a) -> (pi (d :: Num) . 0 < d, d ~ n - m => a) -> a\ntri {0}   {0}   a b c = b\ntri {m+1} {0}   a b c = a {m+1}\ntri {0}   {n+1} a b c = c {n+1}\ntri {m+1} {n+1} a b c = tri {m} {n} a b c", True) :
>   ("f :: forall a . pi (m n :: Num) . a\nf {m} {n} = let h :: m ~ n => a\n                h = h\n            in f {m} {n}", True) :
>   ("f :: forall a (m n :: Num) . (m ~ n => a) -> a\nf x = x", False) :
>   ("f :: forall a (m n :: Num) . ((m ~ n => a) -> a) -> (m ~ n => a) -> a\nf x y = x y", True) :
>   ("f :: forall a (m n :: Num) . ((m ~ n => a) -> a) -> (m ~ n + 1 => a) -> a\nf x y = x y", False) :
>   ("f :: forall a . pi (m n :: Num) . a\nf {m} {n} = let h :: m ~ n => a\n                h = h\n            in h", False) :
>   ("f :: forall a . pi (m n :: Num) . ((m ~ 0 => a) -> a) -> a\nf {m} {n} x = let h :: m ~ n => a\n                  h = h\n            in x h", False) :
>   ("f :: pi (n :: Num) . Integer\nf {n} | {n >= 0} = n\nf {n} | {n < 0} = 0", True) :
>   ("f :: pi (n :: Num) . Integer\nf {n} | {m ~ 0} = n", False) : 
>   ("f :: pi (n :: Num) . Integer\nf {n} | {n > 0, n < 0} = f {n}\nf {n} | True = 0", True) :
>   ("f :: pi (n :: Num) . (n ~ 0 => Integer) -> Integer\nf {n} x | {n ~ 0} = x\nf {n} x = 0", True) : 
>   ("f :: pi (n :: Num) . (n ~ 0 => Integer) -> Integer\nf {n} x | {n ~ 0} = x\nf {n} x = x", False) : 
>   ("x = 0\nx = 1", False) : 
>   ("x :: Integer\nx = 0\nx = 1", False) : 
>   ("x = 0\ny = x\nx = 1", False) : 
>   ("x = y\ny :: Integer\ny = x", True) : 
>   ("x :: forall (a :: * -> *) . a\nx = x", False) : 
>   (vec3Decl ++ "head (Cons x xs) = x\nid2 Nil = Nil\nid2 (Cons x xs) = Cons x xs", False) :
>   (vec3Decl ++ "head :: forall (n :: Num) a. Vec (1+n) a -> a\nhead (Cons x xs) = x\nid2 :: forall (n :: Num) a. Vec n a -> Vec n a\nid2 Nil = Nil\nid2 (Cons x xs) = Cons x xs", True) :
>   (vec3Decl ++ "append :: forall a (m n :: Num) . 0 <= m, 0 <= n, 0 <= (m + n) => Vec m a -> Vec n a -> Vec (m+n) a\nappend Nil ys = ys\nappend (Cons x xs) ys = Cons x (append xs ys)", True) :
>   (vec3Decl ++ "append :: forall a (m n :: Num) . 0 <= n => Vec m a -> Vec n a -> Vec (m+n) a\nappend Nil ys = ys\nappend (Cons x xs) ys = Cons x (append xs ys)", True) :
>   (vec3Decl ++ "tail :: forall (n :: Num) a. Vec (n+1) a -> Vec n a\ntail (Cons x xs) = xs", True) :
>   (vec3Decl ++ "lie :: forall a (n :: Num) . Vec n a\nlie = Nil", False) :
>   (vec3Decl ++ "head :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> a\nhead (Cons x xs) = x", True) :
>   (vec3Decl ++ "silly :: forall a (m :: Num). m <= -1 => Vec m a -> a\nsilly (Cons x xs) = x", True) :
>   (vec3Decl ++ "silly :: forall a (m :: Num). m <= -1 => Vec m a -> a\nsilly (Cons x xs) = x\nbad = silly (Cons Nil Nil)", False) :
>   (vec3Decl ++ "head :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> a\nhead (Cons x xs) = x\nwrong = head Nil", False) :
>   (vec3Decl ++ "head :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> a\nhead (Cons x xs) = x\nright = head (Cons Nil Nil)", True) :
>   (vec3Decl ++ "tail :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> Vec m a\ntail (Cons x xs) = xs\ntwotails :: forall a (m :: Num). 0 <= m, 0 <= (m+1) => Vec (m+2) a -> Vec m a \ntwotails xs = tail (tail xs)", True) :
>   (vec3Decl ++ "tail :: forall a (m :: Num). 0 <= m => Vec (m+1) a -> Vec m a\ntail (Cons x xs) = xs\ntwotails xs = tail (tail xs)", True) :
>   (vec3Decl ++ "f :: forall a (n m :: Num). n ~ m => Vec n a -> Vec m a\nf x = x", True) :
>   (vec3Decl ++ "id2 :: forall a (n :: Num) . Vec n a -> Vec n a\nid2 Nil = Nil\nid2 (Cons x xs) = Cons x xs", True) :
>   (vec3Decl ++ "id2 :: forall a (n m :: Num) . Vec n a -> Vec m a\nid2 Nil = Nil\nid2 (Cons x xs) = Cons x xs", False) :
>   (vec3Decl ++ "id2 :: forall a (n m :: Num) . n ~ m => Vec n a -> Vec m a\nid2 Nil = Nil\nid2 (Cons x xs) = Cons x xs", True) :
>   (vec3Decl ++ "data Pair :: * -> * -> * where Pair :: forall a b. a -> b -> Pair a b\nvsplit2 :: forall (n :: Num) a . pi (m :: Num) . Vec (m + n) a -> Pair (Vec m a) (Vec n a)\nvsplit2 {0}   xs           = Pair Nil xs\nvsplit2 {n+1} (Cons x xs) = let  f (Pair ys zs)  = Pair (Cons x ys) zs\n                                 xs'             = vsplit2 {n} xs\n                             in f xs'", True) :
>   ("data Max :: Num -> Num -> Num -> * where\n  Less :: forall (m n :: Num) . m < n => Max m n n\n  Same :: forall (m :: Num) . Max m m m\n  More :: forall (m n :: Num) . m > n => Max m n m", True) :
>   ("data Int :: Num -> * where\nint :: pi (n :: Num) . Int n\nint = int\ndata Even :: Num -> * where\n  Twice :: pi (n :: Num) . Even (2 * n)\nunEven (Twice {n}) = int {n}", False) :
>   ("data Int :: Num -> * where\nint :: pi (n :: Num) . Int n\nint = int\ndata Even :: Num -> * where\n  Twice :: pi (n :: Num) . Even (2 * n)\nunEven :: forall (n :: Num). Even (2 * n) -> Int n\nunEven (Twice {n}) = int {n}", True) :
>   ("f :: Boo -> Boo\nf x = x\ndata Boo where Boo :: Boo", True) :
>   ("data Ex where Ex :: pi (n :: Num) . Ex\nf :: forall a . (pi (n :: Num) . a) -> Ex -> a\nf g (Ex {n}) = g {n}", True) :
>   ("y = 2\ny :: Integer", True) :
>   ("y = 2\nx = 3\ny :: Integer", True) :
>   ("data UNat :: Num -> * where\ndata Bad :: (Num -> Num) -> * where Eek :: forall (f :: Num -> Num) . UNat (f 0) -> Bad f\nbadder :: forall (g :: Num -> Num -> Num) . Bad (g 1) -> UNat (g (2-1) 0)\nbadder (Eek n) = n", False) :
>   ("narg {n} = n", True) :
>   ("data UNat :: Num -> * where\nunat :: pi (n :: Num) . UNat n\nunat = unat\nnarg {n} = unat {n}", True) :
>   ("data UNat :: Num -> * where\nunat :: pi (n :: Num) . 0 <= n => UNat n\nunat = unat\nnarg {n} = unat {n}", True) :
>   ("data UNat :: Num -> * where\nunat :: pi (n :: Num) . UNat n\nunat = unat\nf :: UNat 0 -> UNat 0\nf x = x\nnarg {n} = f (unat {n})", True) :
>   ("f :: pi (m :: Nat) . Integer\nf {m} = m", True) :
>   ("bad :: forall (m n :: Num) . Integer\nbad | {m ~ n} = 0\nbad | True    = 1", False) :
>   ("worse :: forall (n :: Num) . Integer\nworse = n", False) :
>   ("f :: pi (m :: Num) . Integer\nf = f\nworse :: forall (n :: Num) . Integer\nworse = f {n}", False) :
>   ("f = \\ {x} -> x", True) :
>   ("f = \\ {x} y {z} -> x", True) :
>   ("f = \\ {x} y {z} -> x y", False) :
>   ("f = \\ {x} y {z} -> y x", True) :
>   ("f = \\ {x} y {z} -> y {x}", False) :
>   ("f :: pi (n :: Num) . Integer\nf = \\ {x} -> x", True) :
>   ("f :: forall a . pi (m :: Num) . (Integer -> a) -> a\nf = \\ {x} y -> y x", True) :
>   ("f :: forall a . pi (m :: Num) . (pi (n :: Num) . a) -> a\nf = \\ {x} y -> y {x}", True) :
>   ("f = \\ a -> a\ng = \\ {x} -> f (\\ {y} -> y) {x}", True) :
>   ("f :: (pi (n :: Num) . Integer) -> (pi (n :: Num) . Integer)\nf = \\ a -> a\ng = \\ {x} -> f (\\ {y} -> y) {x}", True) :
>   ("f :: pi (n :: Num) . forall a . a -> a\nf = \\ {n} x -> x", True) :
>   ("f g {n} = g {n}", True) :
>   ("f :: forall a. (pi (n :: Num) . a) -> (pi (n :: Num) . a)\nf g {n} = g {n}", True) :
>   ("f :: pi (n :: Num) . Integer\nf = \\ {n} -> n\ng = \\ {n} -> f {n}", True) :
>   ("f :: pi (n :: Nat) . Integer\nf = \\ {n} -> n\ng = \\ {n} -> f {n}", True) :
>   ("f :: pi (n :: Nat) . Integer\nf = \\ {n} -> n\ng :: pi (n :: Num) . Integer\ng = \\ {n} -> f {n}", False) :
>   ("f :: pi (n :: Nat) . Integer\nf = \\ {n} -> n\ng :: pi (n :: Nat) . Integer\ng = \\ {n} -> f {n}", True) :
>   ("f :: (pi (n :: Nat) . Integer) -> Integer\nf g = g {3}", True):
>   ("f :: (pi (n :: Nat) . Integer) -> Integer\nf h = h {3}\ny :: pi (n :: Nat) . Integer\ny {n} = 3\ng = f (\\ {n} -> y {n})", True):
>   ("data D :: Num -> * where\n  Zero :: D 0\n  NonZero :: forall (n :: Num) . D n\nisZ :: forall a . pi (n :: Num) . (n ~ 0 => a) -> a -> a\nisZ = isZ\nx :: pi (n :: Num) . D n\nx {n} = isZ {n} Zero Zero", False) :
>   ("data D :: Num -> * where\n  Zero :: D 0\n  NonZero :: forall (n :: Num) . D n\nisZ :: forall a . pi (n :: Num) . (n ~ 0 => a) -> a -> a\nisZ = isZ\nx :: pi (n :: Num) . D n\nx {n} = isZ {n} Zero NonZero", True) :
>   -- ("f :: forall (n :: Num) . n <= 42 => Integer\nf = f", True) :
>   ("f :: forall (t :: Num -> *)(n :: Num) . n <= 42 => t n -> Integer\nf = f\ng :: forall (s :: Num -> *) . (forall (n :: Num) . n <= 42 => s n -> Integer) -> Integer\ng = g\nh = g f", True) :
>   ("a :: forall (x :: Num) . Integer\na =\n  let f :: forall (t :: Num -> *)(n :: Num) . n <= x => t n -> Integer\n      f = f\n      g :: forall (s :: Num -> *) . (forall (n :: Num) . n <= x => s n -> Integer) -> Integer\n      g = g\n  in g f", True) :
>   ("noo :: Bool -> Bool\nnoo x = case x of\n  True -> False\n  False -> True", True) :
>   ("noo :: Bool -> Bool\nnoo x = case x of\n  True -> False\n  False -> 3", False) :
>   (vecDecl ++ "f :: forall (n :: Num) a . Vec n a -> Vec n a\nf x = case x of\n  Nil -> Nil\n  Cons x xs -> Cons x xs", True) :
>   ("noo x = case x of\n  True -> False\n  False -> True", True) :
>   ("noo x = case x of\n  True -> False\n  False -> 3", False) :
>   (vecDecl ++ "f x = case x of\n  Nil -> Nil\n  Cons x xs -> Cons x xs", False) :
>   ("f :: forall (t :: Num -> *)(m n :: Num) . t (m * n) -> t (m * n)\nf x = x", True) :
>   ("f :: forall (t :: Num -> *)(m n :: Num) . t (m * n) -> t (n * m)\nf x = x", True) :
>   ("f :: forall (t :: Num -> *)(m n :: Num) . t (m * n) -> t (m + n)\nf x = x", False) :
>   ("f :: forall (f :: Num -> *) . f (min 2 3) -> f (min 3 2)\nf x = x", True) :
>   ("f :: forall (f :: Num -> *) . f (min 2 3) -> f (min 1 2)\nf x = x", False) :
>   ("f :: forall (f :: Num -> *)(a :: Num) . f (max a 3) -> f (max a 3)\nf x = x", True) :
>   ("f :: forall (f :: Num -> *)(a :: Num) . f (max a 3) -> f (max 3 a)\nf x = x", True) :
>   ("f :: forall (f :: Num -> *)(a :: Num) . f (max a 3) -> f (max 2 a)\nf x = x", False) :
>   ("f :: forall (f :: Num -> *)(a b :: Num) . f (min a b) -> f (min b a)\nf x = x", True) :
>   ("f :: forall (f :: Num -> *)(a b c :: Num) . a <= b, b <= c => f (min a b) -> f (min c a)\nf x = x", True) :
>   ("f :: forall (f :: Num -> *)(a b c :: Num) . a >= b, b <= c => f (min a b) -> f (min c a)\nf x = x", False) :
>   ("f :: forall (f :: Num -> *)(a :: Num) . a > 99 => f a -> f (abs a)\nf x = x", True) :
>   ("f :: forall (f :: Num -> *) . f (signum (-6)) -> f (abs (-1) - 2)\nf x = x", True) :
>   ("f :: pi (m :: Num) . Integer\nf {m} = f {abs m}", True) :
>   ("f :: forall (f :: Num -> *)(a :: Num) . f (2 ^ a) -> f (2 ^ a)\nf x = x", True) :
>   ("f :: forall (f :: Num -> *)(a :: Num) . f (a ^ 2) -> f (a ^ 3)\nf x = x", False) :
>   ("f :: forall (f :: Num -> *)(a :: Num) . f (3 ^ 2) -> f 9\nf x = x", True) :
>   ("f :: forall (f :: Num -> *)(a b :: Num) . a ~ b => f (a ^ 1) -> f b\nf x = x", True) :
>   ("f :: pi (m :: Num) . Integer\nf {m} = f {6 ^ 2 + m}", True) :
>   (vec2Decl ++ "append :: forall a (m n :: Num) . Vec a m -> Vec a n -> Vec a (m+n)\nappend = append\nflat :: forall a (m n :: Num). Vec (Vec a m) n -> Vec a (m*n)\nflat Nil = Nil\nflat (Cons xs xss) = append xs (flat xss)", True) :
>   ("f :: pi (x :: Num) . Bool\nf {x} | {x > 0} = True\n      | otherwise = False", True) :
>   ("f {x} | {x > 0} = True\n      | otherwise = False", True) :
>   ("needPos :: pi (x :: Num) . x > 0 => Integer\nneedPos = needPos\nf :: pi (x :: Num) . Integer\nf {x} | {x > 0} = needPos {x}\n      | otherwise = -1", True) :
>   ("needPos :: pi (x :: Num) . x > 0 => Integer\nneedPos = needPos\nf :: pi (x :: Num) . Integer\nf {x} | {x > 0} = needPos {x}\n      | otherwise = needPos {x}", False) :
>   ("needPos :: pi (x :: Num) . x > 0 => Integer\nneedPos = needPos\nf {x} | {x > 0} = needPos {x}\n      | otherwise = -1", True) :
>   ("needPos :: pi (x :: Num) . x > 0 => Integer\nneedPos = needPos\nf {x} | {x > 0} = needPos {x}\n      | otherwise = needPos {x}", True) :
>   ("f x | (case x of True -> False\n                 False -> True\n            ) = 1\n    | otherwise = 0", True) :
>   ("f x | True = 1\n    | False = True", False) :
>   ("f :: forall (f :: Num -> *)(a b :: Num) . f ((a + 2) * b) -> f (b + b + b * a)\nf x = x", True) :
>   ("f :: forall (f :: Num -> *)(a b :: Num) . 0 <= a * b => f a -> f b\nf = f\ng :: forall (f :: Num -> *)(a b :: Num) . 0 <= a, 0 <= b => f a -> f b\ng = f", True) :
>   ("f :: forall (f :: Num -> *)(a b :: Num) . 0 <= a * b + a => f a -> f b\nf = f\ng :: forall (f :: Num -> *)(a b :: Num) . 0 <= a, 0 <= b + 1 => f a -> f b\ng = f", True) :
>   ("f :: forall (f :: Num -> *)(a b :: Num) . 0 <= b + 1 => f a -> f b\nf = f\ng :: forall (f :: Num -> *)(a b :: Num) . 0 <= a, 0 <= a * b + a => f a -> f b\ng = f", True) :
>   ("f :: forall (f :: Num -> *)(a :: Num) . f (a ^ (-1)) -> f (a ^ (-1))\nf x = x", False) :
>   ("f :: forall (f :: Num -> *)(a :: Num) . f (a * a ^ (-1)) -> f 1\nf x = x", False) :
>   ("data Fin :: Num -> * where\ndata Tm :: Num -> * where A :: forall (m :: Num) . 0 <= m => Tm m -> Tm m -> Tm m\nsubst :: forall (m n :: Num) . 0 <= n => (pi (w :: Num) . 0 <= w => Fin (w+m) -> Tm (w + n)) -> Tm m -> Tm n\nsubst s (A f a) = A (subst s f) (subst s a)", True) :
>   ("x = 2 + 3", True) :
>   ("x = 2 - 3", True) :
>   ("x = - 3", True) :
>   ("f :: forall (f :: Num -> *)(a b :: Num) . f (2 ^ (a + b)) -> f (2 ^ a * 2 ^ b)\nf x = x", True) :
>   ("f :: forall (f :: Num -> *)(a b :: Num) . f (2 ^ (2 * a)) -> f ((2 ^ a) ^ 2)\nf x = x", True) :
>   ("f :: forall (f :: (Num -> Num) -> *) . f (min 2) -> f (min 2)\nf x = x", True) :
>   ("f :: forall (f :: Num -> *)(a :: Num) . a ~ 0 => f (0 ^ a) -> f 1\nf x = x", True) :
>   ("f :: forall (f :: * -> Num)(g :: Num -> *) . g (f Integer) -> g (f Integer)\nf x = x", True) :
>   ("f :: forall (f :: Num -> Num -> Num -> Num)(g :: Num -> *) . g (f 1 2 3) -> g (f 1 2 2)\nf x = x", False) :
>   ("f :: Integer", False) :
>   ("x :: forall a . [a]\nx = []", True) :
>   ("y :: [Integer]\ny = 1 : 2 : [3, 4]", True) :
>   ("x = [[]]", True) :
>   ("x = 1 : [] : []", False) :
>   ("x = 1 + 3 : [6]", True) : 
>   ("x :: ()\nx = ()", True) : 
>   ("x :: (Integer, Integer)\nx = ()", False) : 
>   ("x = ((), ())", True) :
>   ("f () = ()\ng (x, y) = (y, x)", True) : 
>   ("f () = ()\nf (x, y) = (y, x)", False) : 
>   ("f xs = case xs of\n      [] -> []\n      y:ys -> y : f ys", True) :
>   ("scanl            :: (a -> b -> a) -> a -> [b] -> [a]\nscanl f q xs     =  q : (case xs of\n                            []   -> []\n                            x:xs -> scanl f (f q x) xs\n                        )", True) :
>   ("a = \"hello\"", True) :
>   ("b w = w : 'o' : 'r' : ['l', 'd']", True) :
>   []
