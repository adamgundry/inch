> {-# LANGUAGE ScopedTypeVariables #-}

> module Language.Inch.File where

> import Prelude hiding (catch)
> import Control.Exception
> import Control.Monad.State
> import System.Exit
> import System.FilePath
> import System.IO

> import Paths_inch (getDataFileName)

> import Language.Inch.Context
> import Language.Inch.Syntax
> import Language.Inch.Parser
> import Language.Inch.PrettyPrinter
> import Language.Inch.ProgramCheck
> import Language.Inch.Erase

> checkFile :: FilePath -> String -> IO (Module (), ZipState)
> checkFile original s = do
>     md <- parseModuleIO
>     ds <- readImports (fst (splitFileName original)) (modImports md)
>     checkModuleIO md ds
>   where
>     parseModuleIO = case parseModule original s of
>         Right md  -> return md
>         Left err  -> putStrLn ("parse error:\n" ++ show err) >> exitFailure
>
>     checkModuleIO md ds = case runStateT (checkModule md ds) initialState of
>         Right x   -> return x
>         Left err  -> putStrLn ("type-checking failed:\n" ++ renderMe err) >> exitFailure


> eraseWrite :: FilePath -> Module () -> ZipState -> IO ()
> eraseWrite output md st = case evalStateT (eraseModule md) st of
>     Right md'  -> writeFile output (renderMe (fog md'))
>     Left err   -> putStrLn ("erase error:\n" ++ renderMe err) >> exitFailure

> getInterface :: Module () -> String
> getInterface = renderMe . map fog . filter dataOrSigDecl . modDecls
>   where
>     dataOrSigDecl (DataDecl _ _ _ _)    = True
>     dataOrSigDecl (Decl (SigDecl _ _))  = True
>     dataOrSigDecl (Decl (FunDecl _ _))  = False


> readImport :: FilePath -> Import -> IO [STopDeclaration ()]
> readImport dir im = do
>     s <- catch (readFile (combine dir inchFile)) $ \ (_ :: IOException) ->
>              catch (readFile =<< getDataFileName inchFile) $ \ (_ :: IOException) ->
>                  hPutStrLn stderr ("Could not load " ++ inchFile) >> return ""
>     case parseInterface inchFile s of
>         Right ds  -> return $ filter (included . topDeclName) ds
>         Left err  -> putStrLn ("interface parse error:\n" ++ show err) >> exitFailure
>   where
>     inchFile = importName im ++ ".inch"
>     included x = case impSpec im of
>         ImpAll        -> True
>         Imp ys        -> x `elem` ys
>         ImpHiding ys  -> x `notElem` ys

> readImports :: FilePath -> [Import] -> IO [STopDeclaration ()]
> readImports dir is = fmap join (mapM (readImport dir) is')
>   where
>     is' = if any (("Prelude" ==) . importName) is then is
>             else Import False "Prelude" Nothing ImpAll : is