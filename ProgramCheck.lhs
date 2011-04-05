> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts #-}

> module ProgramCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Maybe
> import Data.Traversable
> import Text.PrettyPrint.HughesPJ

> import BwdFwd
> import TyNum
> import Kind
> import Type
> import Num
> import Syntax
> import Context
> import Unify
> import Kit
> import Error
> import PrettyPrinter
> import PrettyContext
> import KindCheck
> import TypeCheck


> runCheckProg p = runStateT (checkProg p) initialState

> checkProg :: SProgram -> Contextual () Program
> checkProg xs = do
>     traverse makeDecl xs
>     traverse checkDecl xs
>   where
>     makeDecl :: SDeclaration -> Contextual () ()
>     makeDecl (DD d) = makeTyCon d
>     makeDecl (FD f) = makeBinding f

>     makeTyCon :: SDataDeclaration -> Contextual () ()
>     makeTyCon (DataDecl t k cs) = inLocation (text $ "in data type " ++ t) $
>         case kindKind k of
>           Ex k' -> do
>             unless (targetsSet k') $ errKindTarget k
>             insertTyCon t (Ex k')

>     makeBinding :: SFunDeclaration -> Contextual () ()
>     makeBinding (FunDecl x (Just ty) _) =
>       inLocation (text $ "in binding " ++ x) $ do
>         TK ty' k <- inferKind B0 ty
>         case k of
>           KSet  -> insertBinding x (Just ty')
>           _     -> errKindNotSet (fogKind k)
>     makeBinding (FunDecl x Nothing _) = insertBinding x Nothing

> checkDecl :: SDeclaration -> Contextual () Declaration
> checkDecl (DD d) = DD <$> checkDataDecl d
> checkDecl (FD f) = do
>     f@(FunDecl x (Just ty) _) <- checkFunDecl f 
>     updateBinding x (Just ty)
>     return $ FD f



> checkDataDecl :: SDataDeclaration -> Contextual () DataDeclaration
> checkDataDecl (DataDecl t k cs) = inLocation (text $ "in data type " ++ t) $
>     unEx (kindKind k) $ \ k -> DataDecl t k <$> traverse (checkConstructor t) cs

> checkConstructor :: TyConName -> SConstructor -> Contextual () Constructor
> checkConstructor t (c ::: ty) = inLocation (text $ "in constructor " ++ c) $ do
>     TK ty' k <- inferKind B0 ty
>     case k of
>       KSet -> do
>         unless (ty' `targets` t) $ errConstructorTarget ty
>         insertTmCon c ty'
>         return (c ::: ty')
>       _ -> errKindNotSet (fogKind k)


