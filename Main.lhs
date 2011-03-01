> module Main where

> import Control.Monad.State
> import System

> import Parser
> import PrettyPrinter
> import ProgramCheck
> import Erase


> help me = "Usage: " ++ me ++ " [original file] [input file] [output file]"

> main = do
>     args <- getArgs
>     me <- getProgName
>     case args of
>         [original, input, output] -> do
>             s <- readFile input
>             case preprocess original s of
>                 Right z  -> writeFile output z
>                 Left s   -> putStrLn (me ++ " " ++ s) >> exitFailure
>         _ -> putStrLn $ help me


> preprocess :: String -> String -> Either String String
> preprocess fn s = case parse program fn s of
>     Right p   -> case typeCheck p of
>         Right (p', st) -> case runStateT (eraseProg p') st of
>             Right (p'', st) -> Right $ show (prettyProgram p'')
>             Left err        -> Left $ "erase error:\n" ++ render err ++ "\n"

>         Left err -> Left $ "type-checking failed:\n"
>                             ++ render err ++ "\n"
>     Left err  -> Left $ "parse error:\n" ++ show err ++ "\n"