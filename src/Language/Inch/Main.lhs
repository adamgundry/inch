> module Main where

> import Control.Monad.State
> import System.Environment
> import System.Exit
> import System.FilePath

> import Language.Inch.Context
> import Language.Inch.Syntax
> import Language.Inch.Parser
> import Language.Inch.PrettyPrinter
> import Language.Inch.ProgramCheck
> import Language.Inch.Erase


> help :: String -> String
> help me = "Usage: " ++ me ++ " [original file] [input file] [output file]"

> main :: IO ()
> main = do
>     args <- getArgs
>     me <- getProgName
>     case args of
>         [original, input, output] -> do
>             s <- readFile input
>             case preprocess original s of
>                 Right (y, z)  -> do
>                     writeFile (replaceExtension original ".inch") y
>                     writeFile output z
>                 Left x   -> putStrLn (me ++ " " ++ x) >> exitFailure
>         _ -> putStrLn $ help me

> modHeader :: Maybe String -> String
> modHeader Nothing = ""
> modHeader (Just m) = "module " ++ m ++ " where\n"

> preprocess :: String -> String -> Either String (String, String)
> preprocess fn s = case parseModule fn s of
>     Right md -> case runStateT (checkModule md) initialState of
>         Right (md', st) -> case evalStateT (eraseModule md') st of
>             Right md'' -> Right (sigs p, renderMe (fog md''))
>                 where
>                     Mod _ _ p = md''
>                     sigs    = renderMe . map fog . filter dataOrSigDecl
>                     dataOrSigDecl (SigDecl _ _)       = True
>                     dataOrSigDecl (DataDecl _ _ _ _)  = True
>                     dataOrSigDecl (FunDecl _ _)       = False
>             Left err        -> Left $ "erase error:\n" ++ renderMe err ++ "\n"

>         Left err -> Left $ "type-checking failed:\n"
>                             ++ renderMe err ++ "\n"
>     Left err  -> Left $ "parse error:\n" ++ show err ++ "\n"