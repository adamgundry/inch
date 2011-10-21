> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts #-}

> module Language.Inch.ProgramCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Traversable
> import Text.PrettyPrint.HughesPJ

> import Language.Inch.BwdFwd
> import Language.Inch.Kind
> import Language.Inch.Type
> import Language.Inch.Syntax
> import Language.Inch.Context
> import Language.Inch.Kit
> import Language.Inch.Error
> import Language.Inch.KindCheck
> import Language.Inch.TypeCheck
> import Language.Inch.Check
> import Language.Inch.PrettyPrinter

> assertContextEmpty :: Contextual ()
> assertContextEmpty = do
>     g <- getContext
>     case g of
>         B0  -> return ()
>         _   -> traceContext "assertContextEmpty" >> erk "context is not empty"

> runCheckProg p = runStateT (checkProg p) initialState

> checkProg :: SProgram -> Contextual Program
> checkProg ds = do
>     mapM_ makeTyCon ds
>     mapM_ makeBinding ds
>     concat <$> traverse checkDecl ds
>   where
>     makeTyCon :: SDeclaration () -> Contextual ()
>     makeTyCon (DataDecl t k cs ds) = inLocation (text $ "in data type " ++ t) $
>         case kindKind k of
>           Ex k' -> do
>             unless (targetsSet k') $ errKindTarget k
>             insertTyCon t (Ex k')
>     makeTyCon _ = return ()

> checkDecl :: SDeclaration () -> Contextual [Declaration ()]
> checkDecl (DataDecl t k cs ds) = inLocation (text $ "in data type " ++ t) $ 
>   unEx (kindKind k) $ \ k -> do
>     cs    <- traverse (checkConstructor t) cs
>     return [DataDecl t k cs ds]
> checkDecl d = do
>   assertContextEmpty 
>   ds <- checkInferFunDecl d
>   assertContextEmpty
>   unless (all (goodDecl B0) ds) $ erk $ unlines ("checkDecl: bad declaration" : map (renderMe . fog) ds)
>   return ds

> checkConstructor :: TyConName -> SConstructor -> Contextual Constructor
> checkConstructor t (c ::: ty) = inLocation (text $ "in constructor " ++ c) $ do
>     TK ty' k <- inferKind All B0 (wrapForall [] ty)
>     case k of
>       KSet -> do
>         unless (ty' `targets` t) $ errConstructorTarget ty
>         ty'' <- goGadtMangle ty'
>         insertTmCon c ty''
>         return (c ::: ty'')
>       _ -> errKindNotSet (fogKind k)



> goGadtMangle :: Type KSet -> Contextual (Type KSet)
> goGadtMangle ty = do
>     (ty', vts) <- runWriterT $ makeEqGadtMangle [] ty
>     return $ foldr bindVar ty' (map fst vts)
>   where
>     bindVar :: Var () KNum -> Type KSet -> Type KSet
>     bindVar a = Bind All (fogVar a) KNum . bindTy a

> makeEqGadtMangle :: [Ex (Var ())] -> Type KSet ->
>     ContextualWriter [(Var () KNum, Maybe TypeNum)] (Type KSet)
> makeEqGadtMangle as ty = do
>     (ty', vts) <- lift $ runWriterT $ gadtMangle as ty
>     tell $ map (\ (a, _) -> (a, Nothing)) vts
>     return $ foldr makeEq ty' vts
>   where
>     makeEq :: (Var () KNum, Maybe TypeNum) -> Type KSet -> Type KSet
>     makeEq (a, Just n)   = Qual (TyVar a %==% n)
>     makeEq (a, Nothing)  = id

> gadtMangle :: [Ex (Var ())] -> Type k ->
>     ContextualWriter [(Var () KNum, Maybe TypeNum)] (Type k)
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
>     isAllBound as (TyVar a)
>         | Ex a `elem` as     = Right $ delete (Ex a) as
>         | otherwise          = Left  $ fogVar a ++ "'"
>     isAllBound _  _          = Left "_ga"

>     help :: [Ex (Var ())] -> Type k ->
>                 ContextualWriter [(Var () KNum, Maybe TypeNum)] (Type k)
>     help as (TyCon c k) = pure $ TyCon c k
>     help as (TyApp f s) = do
>         (s', as') <- warp as s
>         TyApp <$> help as' f <*> pure s'

>     warp :: [Ex (Var ())] -> Type k ->
>                 ContextualWriter [(Var () KNum, Maybe TypeNum)]
>                     (Type k, [Ex (Var ())])
>     warp as t = case (isAllBound as t, getTyKind t) of
>         (Right as', _) -> pure (t, as')
>         (Left x, KNum) -> do
>             a <- freshVar SysVar x KNum
>             tell [(a, Just t)]
>             return (TyVar a, as)
>         (Left _, _) -> erk "Non-numeric GADT"

> gadtMangle as t = pure t