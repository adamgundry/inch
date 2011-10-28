> {-# LANGUAGE ScopedTypeVariables #-}

> module Main where

> import Prelude hiding (catch)
> import System.Environment
> import System.FilePath

> import Language.Inch.Syntax
> import Language.Inch.PrettyPrinter
> import Language.Inch.File


> help :: String -> String
> help me = "Usage: " ++ me ++ " [original file] [input file] [output file]\n\
>           \    or " ++ me ++ " [input file]"

> main :: IO ()
> main = do
>     args <- getArgs
>     me <- getProgName
>     case args of
>         [original, input, output] -> do
>             s <- readFile input
>             (md, st) <- checkFile original s
>             writeFile (replaceExtension original ".inch") (getInterface md)
>             eraseWrite output md st
>         [original] -> do
>             s <- readFile original
>             (md, _) <- checkFile original s
>             putStrLn $ renderMe (fog md)
>         _ -> putStrLn $ help me