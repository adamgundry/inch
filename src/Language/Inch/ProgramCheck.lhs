> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts, RankNTypes #-}

> module Language.Inch.ProgramCheck where

> import Control.Applicative hiding (Alternative)
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
> import Language.Inch.ModuleSyntax
> import Language.Inch.Context
> import Language.Inch.Kit
> import Language.Inch.Error
> import Language.Inch.KindCheck
> import Language.Inch.TypeCheck
> import Language.Inch.Check
> import Language.Inch.PrettyPrinter

> checkModule :: SModule -> [STopDeclaration] -> Contextual Module
> checkModule (Mod mh is ds) xs = do
>     mapM_ makeTyCon xs
>     mapM_ (makeTopBinding True) xs
>     mapM_ checkTopDecl' xs
>     mapM_ makeTyCon ds
>     mapM_ (makeTopBinding False) ds
>     ds' <- concat <$> traverse checkTopDecl' ds
>     return $ Mod mh is ds'
>   where
>     checkTopDecl' ds' = assertContextEmpty *> checkTopDecl ds' <* assertContextEmpty 
>
>     makeTyCon :: STopDeclaration -> Contextual ()
>     makeTyCon (DataDecl t k _ _) = inLocation (text "in data type" <+> text t) $
>         case kindKind k of
>           Ex k' -> do
>             unless (targetsSet k') $ errKindTarget k
>             insertTyCon t (Ex k')
>     makeTyCon (TypeDecl x t) = inLocation (text "in type synonym" <+> text x) $ do
>         Ex t' <- checkTySyn B0 t
>         insertTySyn x t'
>     makeTyCon (CDecl x d)  = insertTyCon x (classKind d)
>     makeTyCon (IDecl _ _)  = return ()
>     makeTyCon (Decl _)     = return ()


> checkTySyn :: Bwd (Ex (Var ())) -> STypeSyn -> Contextual (Ex (TySyn ()))
> checkTySyn b (SSynTy t) = do
>     TK t' _ <- inferKind All b t
>     return . Ex $ SynTy t'
> checkTySyn b (SSynAll x k t) = case kindKind k of                               
>     Ex k' -> do
>         v   <- freshVar (UserVar All) x k'
>         Ex t'  <- checkTySyn (b :< Ex v) t
>         return . Ex $ SynAll x k' (bindTySyn v t')


> makeTopBinding :: Bool -> STopDeclaration -> Contextual ()
> makeTopBinding _ (DataDecl _ _ _ _)  = return ()
> makeTopBinding _ (TypeDecl _ _)      = return ()
> makeTopBinding _ (CDecl _ _)         = return ()
> makeTopBinding _ (IDecl _ _)         = return ()
> makeTopBinding b (Decl d)            = makeBinding b d



> checkTopDecl :: STopDeclaration -> Contextual [TopDeclaration]
> checkTopDecl (DataDecl t k cs ds) = checkDataDecl t k cs ds
> checkTopDecl (TypeDecl x _)       = do
>     Ex t' <- lookupTySyn x
>     return [TypeDecl x t']
> checkTopDecl (CDecl x d) = (\ d' -> [CDecl x d']) <$> checkClassDecl x d
> checkTopDecl (IDecl x d) = (\ d' -> [IDecl x d']) <$> checkInstDecl x d
> checkTopDecl (Decl d) = do
>     ds <- checkInferDecl d
>     unless (all (goodDecl B0) ds) $ erk $
>         unlines ("checkTopDecl: bad declaration" : map (renderMe . fog1) ds)
>     return $ map Decl ds


> checkDataDecl ::  TyConName -> SKind -> [TmConName ::: SType] ->
>                      [String] -> Contextual [TopDeclaration]
> checkDataDecl t k cs ds =  inLocation (text $ "in data type " ++ t) $ 
>   unEx (kindKind k) $ \ k' -> do
>     cs'    <- traverse checkConstructor cs
>     mapM_ (checkDerived k') ds
>     return [DataDecl t k' cs' ds]
>   where
>     checkConstructor :: SConstructor -> Contextual Constructor
>     checkConstructor (c ::: ty) = inLocation (text $ "in constructor " ++ c) $ do
>         ty' <- checkKind KSet All B0 (wrapForall [] ty)
>         unless (ty' `targets` t) $ errConstructorTarget ty
>         ty'' <- goGadtMangle ty'
>         insertTmCon c ty''
>         return (c ::: ty'')
> 
>     checkDerived :: Kind k -> ClassName -> Contextual ()
>     checkDerived l x
>       | x `notElem` derivableClasses = erk $ "Cannot derive instance of " ++ x
>       | otherwise = insertInstDecl x =<< instDecl l (TyCon t l)
>                         (\ s -> TyCon x (KSet :-> KConstraint) `TyApp` s)
>                                                 
>     instDecl :: Kind k -> Ty a k -> (Ty a KSet -> Type KConstraint) ->
>                 Contextual (Type KConstraint)
>     instDecl KSet        u f = return $ f u
>     instDecl (k' :-> l)  u f = do
>         v <- freshVar SysVar "_c" k'
>         instDecl l (u `TyApp` TyVar (wkClosedVar v))
>             (\ s -> Bind All "_c" k' (bindTy v (f s)))
>     instDecl _ _ _ = erk "instDecl: bad kind"

>     derivableClasses = ["Eq", "Ord", "Enum", "Bounded", "Show", "Read"] 


> checkClassDecl :: ClassName -> SClassDeclaration -> Contextual ClassDeclaration
> checkClassDecl x (ClassDecl vks ss ms) = inLocation (text $ "in class " ++ x) $ do
>     vks'  <- traverse checkVK vks
>     ss'   <- traverse (checkKind KConstraint All B0) ss
>     ms'   <- traverse (wongle vks') ms
>     putContext B0
>     let d = ClassDecl vks' ss' ms'
>     insertClassDecl x d
>     return d
>   where
>     checkVK :: VarKind RAW () -> Contextual (VarKind OK ())
>     checkVK (VK v k) = case kindKind k of
>         Ex k' -> flip VK k' <$> fresh (UserVar All) v k' Fixed
>
>     wongle :: [VarKind OK ()] -> TmName ::: SType -> Contextual (TmName ::: Type KSet)
>     wongle xs (m ::: t) = inLocation (text $ "in method " ++ m) $ do
>         t' <- checkKind KSet All B0 (wrapForall (map (\ (VK v _) -> nameToString (varName v)) xs) t)
>         let tsc = allWrapVK xs (Qual (applyVK (TyCon x) xs KConstraint) t')
>         insertBinding m (Just tsc, True)
>         -- mtrace $ "foo " ++ show tb ++ "\nbar " ++ show tsc
>         return $ m ::: t'



> checkInstDecl :: ClassName -> SInstDeclaration -> Contextual InstDeclaration
> checkInstDecl x (InstDecl ts cs zs) =
>   inLocation (text "in instance" <+> text x <+> fsep (map prettyHigh ts)) $ do
>       let vs = unions (map (collectUnbound []) ts ++ map (collectUnbound []) cs)
>       vs' <- traverse (\ s -> fresh (UserVar All) s KSet Fixed) vs
>       ClassDecl vks _ _ <- lookupClassDecl x
>       cs' <- traverse checkPrecondition cs 
>       ts' <- traverse (uncurry checkTyKind) (zip vks ts)
>       zs' <- traverse (uncurry (checkMethod ts')) zs
>       insertInstDecl x (allWrapVK (map (\ v -> VK v KSet) vs')
>                            (cs' /=> applys (TyCon x) ts' KConstraint))
>       putContext B0
>       return $ InstDecl ts' cs' zs'
>     where
>       checkPrecondition :: SType -> Contextual (Type KConstraint)
>       checkPrecondition c = do
>           c' <- checkKind KConstraint All B0 c
>           modifyContext (:< Constraint Given c')
>           return c'

>       checkTyKind :: VarKind OK () -> SType -> Contextual (Ex (Ty ()))
>       checkTyKind (VK _ k) t = Ex <$> checkKind k All B0 t 
>
>       checkMethod :: [Ex (Ty ())] -> TmName -> [SAlternative ()] ->
>                          Contextual (TmName, [Alternative ()])
>       checkMethod tys mn as = do
>           (_ ::: qty, _) <- lookupTopBinding mn 
>           (\ as' -> (mn, as')) <$> checkFunDecl (instExTys tys qty) qty mn as
> 
>       instExTys :: [Ex (Ty ())] -> Type k -> Type k
>       instExTys []          t                = t
>       instExTys (Ex u : us) (Bind All _ k t) =
>           hetEq (getTyKind u) k
>               (instExTys us (instTy u t))
>               (error "instExTys: bad")
>       instExTys _ _ = error "instExTys: bad"

> {-
>       instSubst :: [(VarKind OK (), Ex (Ty ()))] -> Var () k -> Type k
>       instSubst [] v = TyVar v
>       instSubst ((VK w _, Ex u) : wus) v
>           | v =?= w    = hetEq (getTyKind u) (varKind v) u (error "instSubst bad")
>                                  
>           | otherwise  = instSubst wus v
> -}



> goGadtMangle :: Type KSet -> Contextual (Type KSet)
> goGadtMangle ty = do
>     (ty', vts) <- runWriterT $ makeEqGadtMangle [] ty
>     return $ foldr bindVarWrap ty' (map fst vts)
>   where
>     bindVarWrap :: Var () KNum -> Type KSet -> Type KSet
>     bindVarWrap a = Bind All (fogVar a) KNum . bindTy a

> makeEqGadtMangle :: [Ex (Var ())] -> Type KSet ->
>     ContextualWriter [(Var () KNum, Maybe TypeNum)] (Type KSet)
> makeEqGadtMangle as ty = do
>     (ty', vts) <- lift $ runWriterT $ gadtMangle as ty
>     tell $ map (\ (a, _) -> (a, Nothing)) vts
>     return $ foldr makeEq ty' vts
>   where
>     makeEq :: (Var () KNum, Maybe TypeNum) -> Type KSet -> Type KSet
>     makeEq (a, Just n)   = Qual (tyPred EL (TyVar a) n)
>     makeEq (_, Nothing)  = id

> gadtMangle :: [Ex (Var ())] -> Type k ->
>     ContextualWriter [(Var () KNum, Maybe TypeNum)] (Type k)
> gadtMangle as (Qual p t) = Qual p <$> gadtMangle as t
> gadtMangle as (Bind b x k t) = do
>     a <- freshVar SysVar x k
>     let as' = case b of
>                   All -> Ex a : as
>                   _   -> as
>         t' = unbindTy a t
>     case getTyKind t' of
>         KSet -> do
>             t'' <- makeEqGadtMangle as' t'
>             return $ Bind b x k (bindTy a t'')
>         l -> errKindNotSet (fogKind l)

> gadtMangle as (TyApp (TyApp Arr s) t) =
>     TyApp (TyApp Arr s) <$> gadtMangle as t

> gadtMangle xs (TyApp f s) = help xs (TyApp f s)
>   where
>     isAllBound :: [Ex (Var ())] -> Type k -> Either String [Ex (Var ())]
>     isAllBound as (TyVar a)
>         | Ex a `elem` as     = Right $ delete (Ex a) as
>         | otherwise          = Left  $ fogVar a ++ "'"
>     isAllBound _  _          = Left "_ga"

>     help :: [Ex (Var ())] -> Type k ->
>                 ContextualWriter [(Var () KNum, Maybe TypeNum)] (Type k)
>     help _  (TyCon c k) = pure $ TyCon c k
>     help as (TyApp g t) = do
>         (t', as') <- warp as t
>         TyApp <$> help as' g <*> pure t'
>     help _ t = error $ "gadtMangle.help: malformed type " ++ show t

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

> gadtMangle _ t = pure t