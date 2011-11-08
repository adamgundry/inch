> {-# LANGUAGE TypeOperators, MultiParamTypeClasses, TypeSynonymInstances,
>              GADTs, TypeFamilies, UndecidableInstances, ImpredicativeTypes #-}

> module Language.Inch.Erase where

> import Control.Applicative hiding (Alternative)
> import Data.Traversable

> import Language.Inch.Error
> import Language.Inch.Kit
> import Language.Inch.Kind
> import Language.Inch.Type
> import Language.Inch.Syntax
> import Language.Inch.Context


> eraseKind :: Kind k -> Maybe (Ex Kind)
> eraseKind KSet       = Just $ Ex KSet
> eraseKind KNum       = Nothing
> eraseKind KConstraint = Just $ Ex KConstraint
> eraseKind (k :-> l)  =
>     case (eraseKind k, eraseKind l) of
>         (_,             Nothing)       -> Nothing
>         (Nothing,       Just (Ex l'))  -> Just $ Ex l'
>         (Just (Ex k'),  Just (Ex l'))  -> Just $ Ex $ k' :-> l'


> willErase :: Kind k -> Bool
> willErase KSet       = False
> willErase KNum       = True
> willErase KConstraint = False
> willErase (_ :-> l)  = willErase l

> eraseType :: Type k -> Contextual (Ex Kind, TyKind)
> eraseType (TyVar (FVar a k))    = 
>     case eraseKind k of
>         Just (Ex l)  -> return (Ex k, TK (TyVar (FVar a l)) l)
>         Nothing      -> error $ "eraseType: failed to erase kind " ++ show k
> eraseType (TyVar (BVar b)) = impossibleBVar b
> eraseType (TyCon c k)  =
>     case eraseKind k of
>         Just (Ex l) -> return (Ex k, TK (TyCon c l) l)
>         Nothing      -> error $ "eraseType: failed to erase kind " ++ show k
> eraseType (TyApp f s)  = do
>         (Ex k, TK f' kf) <- eraseType f
>         case (k, kf) of
>             (k' :-> l, _) | willErase k'  -> return (Ex l, TK f' kf)
>             (_ :-> l, k'' :-> l'')    -> do
>                 (_, TK s' ks) <- eraseType s
>                 hetEq k'' ks (return (Ex l, TK (TyApp f' s') l''))
>                             (erk "Kind mismatch")
>             _ -> error "eraseType: ill-kinded application"
> eraseType Arr = return $ (Ex (KSet :-> KSet :-> KSet),
>                           TK Arr (KSet :-> KSet :-> KSet))
> eraseType (Bind Pi _ KNum t)   = do
>     (Ex KSet, TK t' KSet) <- eraseType $ unbindTy (error "eraseType: erk") t
>     return (Ex KSet, TK (insertNumArrow t') KSet)
>   where
>     insertNumArrow :: Ty a KSet -> Ty a KSet
>     insertNumArrow (Bind All x k t') = Bind All x k (insertNumArrow t')
>     insertNumArrow t' = tyInteger --> t'
> eraseType (Bind All x k t)        = 
>     case eraseKind k of
>         Just (Ex k') -> do
>             an <- fresh SysVar x k Hole
>             (ek, TK t' KSet) <- eraseType (unbindTy an t)
>             return (ek, TK (Bind All x k' (bindTy (FVar (varName an) k') t')) KSet)
>         Nothing -> eraseType $ unbindTy (error "eraseType: erk") t
> eraseType (Qual _ t) = eraseType t

> eraseType t = error $ "eraseType: illegal type " ++ show t

> eraseToSet :: Type k -> Contextual (Type KSet)
> eraseToSet t = do
>     (_, TK t' KSet) <- eraseType t
>     return t'


> eraseTm :: Term () -> Contextual (Term ())
> eraseTm (TmVar x)    = pure $ TmVar x
> eraseTm (TmCon c)    = pure $ TmCon c
> eraseTm (TmInt k)    = pure $ TmInt k
> eraseTm (CharLit c)  = pure $ CharLit c
> eraseTm (StrLit s)   = pure $ StrLit s
> eraseTm (TmUnOp o)   = pure $ TmUnOp o
> eraseTm (TmBinOp o)  = pure $ TmBinOp o
> eraseTm (TmComp c)   = pure $ TmComp c
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
>     ty' <- eraseToSet ty
>     return $ t' :? ty'

> numToTm :: Type KNum -> Term ()
> numToTm (TyVar x)  = TmVar . fogVar $ x
> numToTm (TyInt i)  = TmInt i
> numToTm (TyApp (UnOp o) m) = TmApp (TmUnOp o) (numToTm m)
> numToTm (TyApp (TyApp (BinOp o) m) n) = TmApp (TmApp (TmBinOp o) (numToTm m)) (numToTm n)
> numToTm t = error $ "numToTm: illegal type " ++ show t


> eraseCon :: Constructor -> Contextual Constructor
> eraseCon (c ::: t) = (c :::) <$> eraseToSet t

> eraseAlt :: Alternative () -> Contextual (Alternative ())
> eraseAlt (Alt ps gt) = do
>     (ps', f)  <- erasePatList ps
>     gt'       <- eraseGuardTerms (renameTypes f gt)
>     return $ Alt ps' gt'

> eraseCaseAlt :: CaseAlternative () -> Contextual (CaseAlternative ())
> eraseCaseAlt (CaseAlt p gt) = do
>     (p', f)  <- erasePat p
>     gt'      <- eraseGuardTerms (renameTypes f gt)
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
>     toTm (P c m n) = TmApp (TmApp (TmComp c) (numToTm m)) (numToTm n)
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
> erasePat (PatNPlusK n k) = return (PatNPlusK n k, id)

> erasePatList :: PatternList a b -> Contextual (PatternList () (), forall k . Var b k -> Var a k)
> erasePatList P0         = return (P0, id)
> erasePatList (p :! ps)  = do
>     (p',   f) <- erasePat p
>     (ps',  g) <- erasePatList ps
>     return (p' :! ps', f . g)

> eraseDecl :: Declaration () -> Contextual (Declaration ())
> eraseDecl (DataDecl s k cs ds) =
>     case eraseKind k of
>         Just (Ex k') -> do
>             cs' <- traverse eraseCon cs
>             return $ DataDecl s k' cs' ds
>         Nothing -> error $ "eraseType: failed to erase kind " ++ show k
> eraseDecl (FunDecl x ps) =
>     FunDecl x <$> traverse eraseAlt ps
> eraseDecl (SigDecl x ty) = SigDecl x <$> eraseToSet ty

> eraseModule :: Module () -> Contextual (Module ())
> eraseModule (Mod mh is ds) = Mod mh is <$> traverse eraseDecl ds
