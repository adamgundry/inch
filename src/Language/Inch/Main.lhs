> module Main where

> import Control.Monad.State
> import System.Environment
> import System.Exit

> import Language.Inch.Parser
> import Language.Inch.PrettyPrinter
> import Language.Inch.ProgramCheck
> import Language.Inch.Erase


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


> modHeader Nothing = ""
> modHeader (Just m) = "module " ++ m ++ " where\n"

> preprocess :: String -> String -> Either String String
> preprocess fn s = case parseProgram fn s of
>     Right (p, mn) -> case runCheckProg p of
>         Right (p', st) -> case runStateT (eraseProg p') st of
>             Right (p'', st) -> Right $ modHeader mn ++ show (prettyProgram p'')
>             Left err        -> Left $ "erase error:\n" ++ renderMe err ++ "\n"

>         Left err -> Left $ "type-checking failed:\n"
>                             ++ renderMe err ++ "\n"
>     Left err  -> Left $ "parse error:\n" ++ show err ++ "\n"