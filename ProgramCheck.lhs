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
>         ty'' <- goGadtMangle ty'
>         insertTmCon c ty''
>         return (c ::: ty'')
>       _ -> errKindNotSet (fogKind k)



> goGadtMangle :: Type k -> Contextual () (Type k)
> goGadtMangle ty = do
>     (ty', vts) <- runWriterT $ makeEqGadtMangle [] ty
>     return $ foldr bindVar ty' (map fst vts)
>   where
>     bindVar :: Var () KNum -> Type k -> Type k
>     bindVar a = Bind All (varToString a) KNum . bindTy a

> makeEqGadtMangle :: [Ex (Var ())] -> Type k ->
>     ContextualWriter [(Var () KNum, Maybe TypeNum)] () (Type k)
> makeEqGadtMangle as ty = do
>     (ty', vts) <- lift $ runWriterT $ gadtMangle as ty
>     tell $ map (\ (a, _) -> (a, Nothing)) vts
>     return $ foldr makeEq ty' vts
>   where
>     makeEq :: (Var () KNum, Maybe TypeNum) -> Type k -> Type k
>     makeEq (a, Just n)   = Qual (NumVar a %==% n)
>     makeEq (a, Nothing)  = id

> gadtMangle :: [Ex (Var ())] -> Type k ->
>     ContextualWriter [(Var () KNum, Maybe TypeNum)] () (Type k)
> gadtMangle as (Qual p t) = Qual p <$> gadtMangle as t
> gadtMangle as (Bind b x k t) = do
>     a <- freshVar SysVar x k
>     let as' = case b of
>                   All -> Ex a : as
>                   _   -> as
>     t' <- makeEqGadtMangle as' (unbindTy a t)
>     return $ Bind b x k (bindTy a t')

> gadtMangle as (TyApp (TyApp Arr s) t) =
>     TyApp (TyApp Arr s) <$> gadtMangle as t

> gadtMangle as (TyApp f s) = help as (TyApp f s)
>   where
>     isAllBound :: [Ex (Var ())] -> Type k -> Either String [Ex (Var ())]
>     isAllBound as (TyNum (NumVar a))
>         | Ex a `elem` as     = Right $ delete (Ex a) as
>         | otherwise          = Left  $ varToString a ++ "'"
>     isAllBound as (TyVar a)
>         | Ex a `elem` as     = Right $ delete (Ex a) as
>         | otherwise          = Left  $ varToString a ++ "'"
>     isAllBound _  (TyNum _)  = Left "_gn"
>     isAllBound _  _          = Left "_ga"

>     help :: [Ex (Var ())] -> Type k ->
>                 ContextualWriter [(Var () KNum, Maybe TypeNum)] () (Type k)
>     help as (TyCon c k) = pure $ TyCon c k
>     help as (TyApp f s) = do
>         (s', as') <- warp as s
>         TyApp <$> help as' f <*> pure s'

>     warp :: [Ex (Var ())] -> Type k ->
>                 ContextualWriter [(Var () KNum, Maybe TypeNum)] ()
>                     (Type k, [Ex (Var ())])
>     warp as t = case (isAllBound as t, getTyKind t) of
>         (Right as', _) -> pure (t, as')
>         (Left x, KNum) -> do
>             a <- freshVar SysVar x KNum
>             tell [(a, Just (toNum t))]
>             return (TyNum (NumVar a), as)
>         (Left _, _) -> erk "Non-numeric GADT"

> gadtMangle as t = pure t