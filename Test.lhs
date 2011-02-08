> module Test where

> import Text.PrettyPrint.HughesPJ
> import qualified Text.ParserCombinators.Parsec.IndentParser as I

> import Parser
> import PrettyPrinter
> import Syntax
> import TypeCheck


> roundTrip :: String -> String -> String
> roundTrip name s = case I.parse program name s of
>     Right prog  ->
>         let s' = show $ prettyHigh prog in
>         case I.parse program name s' of
>             Right prog'
>               | prog == prog'  ->
>                 name ++ " PASS\n" ++ show (prettyHigh prog')
>               | otherwise      ->
>                 name ++ " FAIL: round trip mismatch:\n"
>                      ++ s ++ "\n" ++ s' ++ "\n" ++ show prog ++ "\n" ++ show prog'
>             Left err ->
>                 name ++ " FAIL: round trip re-parse:\n" ++ s' ++ "\n" ++ show err
>     Left err    -> name ++ " FAIL: initial parse:\n" ++ show err

> test s = putStrLn (roundTrip "test" s)
> halfTest s = I.parse program "test" s
> parseCheck s = putStrLn $ case I.parse program "parseCheck" s of
>     Right p   -> case typeCheck p of
>         Right (p', (_, (), c)) -> "Typechecked program\n" ++ show (prettyHigh p')
>                                       ++ "\nin context\n" ++ show c
>         Left err -> "Typecheck error: " ++ err
>     Left err  -> "Parse error: " ++ show err

> validTestData = 
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
>   "f = x :: forall (a :: *) . a" :
>   "f = x :: forall a . a" :
>   "f = x :: forall a b c . a" :
>   "f = x :: forall (a :: Nat)b(c :: * -> *)(d :: *) . a" :
>   "f = x :: forall a b . pi (c :: Nat) d . b -> c" :
>   "f = x :: forall (a b c :: *) . a" :
>   "f x y z = x y z" :
>   "f Con = (\\ x -> x) :: (->) a a" :
>   "f Con = \\ x -> x :: (->) a" :
>   "plus Zero n = n\nplus (Suc m) n = Suc (plus m n)" :
>   "data Nat where Zero :: Nat\n Suc :: Nat -> Nat" :
>   "data Foo :: (* -> *) -> (Nat -> *) where Bar :: forall (f :: * -> *)(n :: Nat) . (Vec (f Int) n -> a b) -> Foo f n" :
>   []


> runTests i [] = []
> runTests i (s:ss) = roundTrip (show i) s : runTests (i+1) ss

> testValid = mapM_ putStrLn $ runTests 0 validTestData