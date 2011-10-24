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


> help me = "Usage: " ++ me ++ " [original file] [input file] [output file]"

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
>                 Left s   -> putStrLn (me ++ " " ++ s) >> exitFailure
>         _ -> putStrLn $ help me


> modHeader Nothing = ""
> modHeader (Just m) = "module " ++ m ++ " where\n"

> preprocess :: String -> String -> Either String (String, String)
> preprocess fn s = case parseModule fn s of
>     Right mod -> case runStateT (checkModule mod) initialState of
>         Right (mod', st) -> case evalStateT (eraseModule mod') st of
>             Right mod'' -> Right (sigs p, renderMe (fog mod''))
>                 where
>                     Mod _ _ p = mod''
>                     sigs    = renderMe . map fog . filter dataOrSigDecl
>                     dataOrSigDecl (SigDecl _ _)       = True
>                     dataOrSigDecl (DataDecl _ _ _ _)  = True
>                     dataOrSigDecl (FunDecl _ _)       = False
>             Left err        -> Left $ "erase error:\n" ++ renderMe err ++ "\n"

>         Left err -> Left $ "type-checking failed:\n"
>                             ++ renderMe err ++ "\n"
>     Left err  -> Left $ "parse error:\n" ++ show err ++ "\n"