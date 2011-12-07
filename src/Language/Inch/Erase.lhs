> {-# LANGUAGE TypeOperators, MultiParamTypeClasses, TypeSynonymInstances,
>              GADTs, TypeFamilies, UndecidableInstances, ImpredicativeTypes #-}

> module Language.Inch.Erase where

> import Control.Applicative hiding (Alternative)
> import Data.Traversable
> import Text.PrettyPrint.HughesPJ

> import Language.Inch.Error
> import Language.Inch.Kit
> import Language.Inch.Kind
> import Language.Inch.Type
> import Language.Inch.Syntax
> import Language.Inch.ModuleSyntax
> import Language.Inch.Context
> import Language.Inch.PrettyPrinter


> eraseKind :: Kind k -> Maybe (Ex Kind)
> eraseKind KSet         = Just $ Ex KSet
> eraseKind KNum         = Nothing
> eraseKind KConstraint  = Just $ Ex KConstraint
> eraseKind (k :-> l)    =
>     case (eraseKind k, eraseKind l) of
>         (_,             Nothing)       -> Nothing
>         (Nothing,       Just (Ex l'))  -> Just $ Ex l'
>         (Just (Ex k'),  Just (Ex l'))  -> Just $ Ex $ k' :-> l'


> willErase :: Kind k -> Bool
> willErase KSet         = False
> willErase KNum         = True
> willErase KConstraint  = False
> willErase (_ :-> l)    = willErase l

> eraseType :: Type k -> Contextual (Maybe TyKind)
> eraseType (TyVar (FVar a k))  = return (eraseKind k >>= \ (Ex l) ->
>                                                  Just (TK (TyVar (FVar a l)) l))
> eraseType (TyVar (BVar b))    = impossibleBVar b
> eraseType (TyCon c k)         = return (eraseKind k >>= \ (Ex l) ->
>                                                  Just (TK (TyCon c l) l))
> eraseType (TySyn x t) = do
>     mt <- eraseTypeSyn t
>     case mt of
>         Nothing       -> return Nothing
>         Just (Ex t')  -> return . Just $ TK (TySyn x t') (getTySynKind t')
> eraseType (TyApp f s)  = do
>         k :-> _ <- return $ getTyKind f
>         mtk <- eraseType f
>         if willErase k
>             then return mtk
>             else case mtk of
>                 Just (TK f' (k'' :-> l'')) -> do
>                     Just (TK s' ks) <- eraseType s
>                     hetEq k'' ks (return (Just (TK (TyApp f' s') l'')))
>                                  (erk "Kind mismatch")
>                 _ -> return Nothing
> eraseType Arr = return . Just $ TK Arr (KSet :-> KSet :-> KSet)
> eraseType (Bind Pi x KNum t)   = do
>     Just (TK t' KSet) <- eraseType $ unbindTy (FVar (N x (error "eraseType: erk") (UserVar Pi)) KNum) t
>     return . Just $ TK (insertNumArrow t') KSet
>   where
>     insertNumArrow :: Ty a KSet -> Ty a KSet
>     insertNumArrow (Bind All y k t') = Bind All y k (insertNumArrow t')
>     insertNumArrow t' = tyInteger --> t'
> eraseType (Bind All x k t)        = 
>     case eraseKind k of
>         Just (Ex k') -> do
>             an <- fresh SysVar x k Hole
>             Just (TK t' l) <- eraseType (unbindTy an t)
>             return . Just $ TK (Bind All x k' (bindTy (FVar (varName an) k') t')) l
>         Nothing -> eraseType $ unbindTy (FVar (N x (error "eraseType: erk") (UserVar All)) k) t
> eraseType (Qual q t) = do
>     q'   <- eraseTo KConstraint q
>     mtk  <- eraseType t
>     return $ (\ (TK t' k') -> TK (qual q' t') k') <$> mtk
>   where
>     qual :: Type KConstraint -> Type k -> Type k
>     qual p u | isTrivial p  = u
>              | otherwise    = Qual p u

> eraseType (TyComp _) = return . Just $ TK tyTrivial KConstraint

> eraseType _ = return Nothing



> eraseTypeSyn :: TypeSyn l -> Contextual (Maybe (Ex (TySyn ())))
> eraseTypeSyn (SynTy t) = do
>     mtk <- eraseType t
>     case mtk of
>        Nothing         -> return Nothing
>        Just (TK t' _)  -> return (Just (Ex (SynTy t')))
> eraseTypeSyn (SynAll x k t) = case eraseKind k of
>     Nothing -> eraseTypeSyn $ unbindTySyn (FVar (N x (error "eraseTypeSyn: erk") (UserVar All)) k) t
>     Just (Ex k') -> do
>         a <- fresh SysVar x k Hole
>         Just (Ex t') <- eraseTypeSyn (unbindTySyn a t)
>         return . Just . Ex $ SynAll x k' (bindTySyn (FVar (varName a) k') t')



> eraseTo :: Kind l -> Type k -> Contextual (Type l)
> eraseTo l t = inLocation (text "when erasing" <+> prettyHigh (fogTy t)
>                               <+> text "to" <+> prettyHigh (fogKind l)) $ do
>     Just (TK t' k') <- eraseType t
>     hetEq k' l (return t')
>                (errKindMismatch (fogTy t' ::: fogKind k') (fogKind l))


> eraseTm :: Term () -> Contextual (Term ())
> eraseTm (TmVar x)    = pure $ TmVar x
> eraseTm (TmCon c)    = pure $ TmCon c
> eraseTm (TmInt k)    = pure $ TmInt k
> eraseTm (CharLit c)  = pure $ CharLit c
> eraseTm (StrLit s)   = pure $ StrLit s
> eraseTm (TmApp f s)  = TmApp <$> eraseTm f <*> eraseTm s
> eraseTm (TmBrace n)  = pure $ numToTm n
> eraseTm (Lam x b)    = Lam x <$> eraseTm b
> eraseTm (NumLam n b)  = do
>     a <- fresh (UserVar Pi) n KNum Hole
>     Lam n <$> eraseTm (unbindTm a b)
> eraseTm (Let ds t)   = Let <$> traverse eraseDecl ds <*> eraseTm t
> eraseTm (Case t as)  = Case <$> eraseTm t <*> traverse eraseCaseAlt as
> eraseTm (t :? ty)    = do
>     t' <- eraseTm t
>     ty' <- eraseTo KSet ty
>     return $ t' :? ty'

> numToTm :: Type KNum -> Term ()
> numToTm (TyVar x)  = TmVar . fogVar $ x
> numToTm (TyInt i)  = TmInt i
> numToTm (TyApp (UnOp o) m) = tmUnOp o (numToTm m)
> numToTm (TyApp (TyApp (BinOp o) m) n) = tmBinOp o (numToTm m) (numToTm n)
> numToTm t = error $ "numToTm: illegal type " ++ show t


> eraseCon :: Constructor -> Contextual Constructor
> eraseCon (c ::: t) = (c :::) <$> eraseTo KSet t

> eraseAlt :: Alternative () -> Contextual (Alternative ())
> eraseAlt (Alt ps gt) = do
>     (ps', f)  <- erasePatList ps
>     gt'       <- eraseGuardTerms (renameTypes1 f gt)
>     return $ Alt ps' gt'

> eraseCaseAlt :: CaseAlternative () -> Contextual (CaseAlternative ())
> eraseCaseAlt (CaseAlt p gt) = do
>     (p', f)  <- erasePat p
>     gt'      <- eraseGuardTerms (renameTypes1 f gt)
>     return $ CaseAlt p' gt'

> eraseGuardTerms :: GuardTerms () -> Contextual (GuardTerms ())
> eraseGuardTerms (Unguarded e ds) = Unguarded <$> eraseTm e
>                                    <*> traverse eraseDecl ds
> eraseGuardTerms (Guarded gts ds) = Guarded <$> traverse er gts
>                                    <*> traverse eraseDecl ds
>   where er (g :*: t) = (eraseGuard g :*:) <$> eraseTm t

> eraseGuard :: Guard () -> Guard ()
> eraseGuard (NumGuard ps)  = ExpGuard (map toTm ps)
>   where
>     toTm (P c m n) = tmComp c (numToTm m) (numToTm n)
>     toTm (_ :=> _) = error "eraseGuard.toTm: implications are not allowed!"
> eraseGuard g              = g

> erasePat :: Pattern a b -> Contextual (Pattern () (), forall k . Var b k -> Var a k)
> erasePat (PatVar v)      = return (PatVar v, id)
> erasePat (PatCon c ps)   = do
>     (ps', f) <- erasePatList ps
>     return (PatCon c ps', f)
> erasePat PatIgnore       = return (PatIgnore, id)
> erasePat (PatBrace a 0)  = do
>     x <- fresh (UserVar Pi) a KNum Hole
>     return (PatVar a, unbindVar (wkClosedVar x))
> erasePat (PatBrace a k)  = do
>     x <- fresh (UserVar Pi) a KNum Hole
>     return (PatNPlusK a k, unbindVar (wkClosedVar x))

> erasePat (PatBraceK k)   = return (PatIntLit k, id)
> erasePat (PatIntLit i)   = return (PatIntLit i, id)
> erasePat (PatCharLit c)  = return (PatCharLit c, id)
> erasePat (PatStrLit s)   = return (PatStrLit s, id)
> erasePat (PatNPlusK n k) = return (PatNPlusK n k, id)

> erasePatList :: PatternList a b -> Contextual (PatternList () (), forall k . Var b k -> Var a k)
> erasePatList P0         = return (P0, id)
> erasePatList (p :! ps)  = do
>     (p',   f) <- erasePat p
>     (ps',  g) <- erasePatList ps
>     return (p' :! ps', f . g)

> eraseTopDecl :: TopDeclaration -> Contextual TopDeclaration
> eraseTopDecl (DataDecl s k cs ds) =
>     case eraseKind k of
>         Just (Ex k') -> do
>             cs' <- traverse eraseCon cs
>             return $ DataDecl s k' cs' ds
>         Nothing -> error $ "eraseTopDecl: failed to erase kind " ++ show k
> eraseTopDecl (TypeDecl x t) = do
>     mt <- eraseTypeSyn t
>     case mt of
>         Nothing       -> return $ TypeDecl x (SynTy tyUnit)
>         Just (Ex t')  -> return $ TypeDecl x t'
> eraseTopDecl (CDecl x d)  = CDecl x <$> eraseClassDecl d
> eraseTopDecl (IDecl x d)  = IDecl x <$> eraseInstDecl d
> eraseTopDecl (Decl d)     = Decl <$> eraseDecl d

> eraseClassDecl :: ClassDeclaration -> Contextual ClassDeclaration
> eraseClassDecl (ClassDecl vs ss ms) = do
>     let vs' = filter (\ (VK _ k) -> not (willErase k)) vs
>     ss' <- traverse (eraseTo KConstraint) ss
>     ms' <- traverse (\ (mn ::: ty) -> (mn :::) <$> eraseTo KSet ty) ms
>     return $ ClassDecl vs' ss' ms'

> eraseInstDecl :: InstDeclaration -> Contextual InstDeclaration
> eraseInstDecl (InstDecl ts cs zs) = return $ (InstDecl ts cs zs)

> eraseDecl :: Declaration () -> Contextual (Declaration ())
> eraseDecl (FunDecl x ps) =
>     FunDecl x <$> traverse eraseAlt ps
> eraseDecl (SigDecl x ty) = SigDecl x <$> eraseTo KSet ty

> eraseModule :: Module -> Contextual Module
> eraseModule (Mod mh is ds) = Mod mh is <$> traverse eraseTopDecl ds
