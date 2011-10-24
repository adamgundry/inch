> {-# LANGUAGE TypeOperators, MultiParamTypeClasses, TypeSynonymInstances,
>              GADTs, TypeFamilies, UndecidableInstances #-}

> module Language.Inch.Erase where

> import Control.Applicative hiding (Alternative)
> import Data.Traversable
> import Unsafe.Coerce

> import Language.Inch.Error
> import Language.Inch.Kit
> import Language.Inch.Kind
> import Language.Inch.Type
> import Language.Inch.Syntax
> import Language.Inch.Context


> eraseKind :: Kind k -> Maybe (Ex Kind)
> eraseKind KSet       = Just $ Ex KSet
> eraseKind KNum       = Nothing
> eraseKind (k :-> l)  =
>     case (eraseKind k, eraseKind l) of
>         (_,             Nothing)       -> Nothing
>         (Nothing,       Just (Ex l'))  -> Just $ Ex l'
>         (Just (Ex k'),  Just (Ex l'))  -> Just $ Ex $ k' :-> l'


> willErase :: Kind k -> Bool
> willErase KSet = False
> willErase KNum = True
> willErase (k :-> l) = willErase l

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
>             (k' :-> l, k'' :-> l'')    -> do
>                 (_, TK s' ks) <- eraseType s
>                 hetEq k'' ks (return (Ex l, TK (TyApp f' s') l''))
>                             (erk "Kind mismatch")
>             _ -> error "eraseType: ill-kinded application"
> eraseType Arr = return $ (Ex (KSet :-> KSet :-> KSet),
>                           TK Arr (KSet :-> KSet :-> KSet))
> eraseType (Bind Pi x KNum t)   = do
>     (Ex KSet, TK t' KSet) <- eraseType $ unbindTy (error "eraseType: erk") t
>     return (Ex KSet, TK (insertNumArrow t') KSet)
>   where
>     insertNumArrow :: Ty a KSet -> Ty a KSet
>     insertNumArrow (Bind All x k t) = Bind All x k (insertNumArrow t)
>     insertNumArrow t = tyInteger --> t
> eraseType (Bind All x k t)        = 
>     case eraseKind k of
>         Just (Ex k') -> do
>             an <- fresh SysVar x k Hole
>             (ek, TK t' KSet) <- eraseType (unbindTy an t)
>             return (ek, TK (Bind All x k' (bindTy (FVar (varName an) k') t')) KSet)
>         Nothing -> eraseType $ unbindTy (error "eraseType: erk") t
> eraseType (Qual p t) = eraseType t

> eraseType t = error $ "eraseType: illegal type " ++ show t

> eraseToSet t = do
>     (_, TK t KSet) <- eraseType t
>     return t


> eraseTm :: Term () -> Contextual (Term ())
> eraseTm (TmVar x)    = pure $ TmVar x
> eraseTm (TmCon c)    = pure $ TmCon c
> eraseTm (TmInt k)    = pure $ TmInt k
> eraseTm (CharLit c)  = pure $ CharLit c
> eraseTm (StrLit s)   = pure $ StrLit s
> eraseTm (TmUnOp o)   = pure $ TmUnOp o
> eraseTm (TmBinOp o)  = pure $ TmBinOp o
> eraseTm (TmApp f s)  = TmApp <$> eraseTm f <*> eraseTm s
> eraseTm (TmBrace n)  = pure $ numToTm n
> eraseTm (Lam x b)    = Lam x <$> eraseTm b
> eraseTm (NumLam n b)  = do
>     a <- fresh (UserVar Pi) n KNum Hole
>     Lam n <$> eraseTm (unbindTm a b)
> eraseTm (Let ds t)   = Let <$> traverse eraseDecl ds <*> eraseTm t
> eraseTm (Case t as)  = Case <$> eraseTm t <*> traverse eraseCaseAlt as
> eraseTm (t :? ty)    = do
>     t <- eraseTm t
>     ty <- eraseToSet ty
>     return $ t :? ty

> numToTm :: Type KNum -> Term ()
> numToTm (TyVar x)  = TmVar . fogVar $ x
> numToTm (TyInt i)  = TmInt i
> numToTm (TyApp (UnOp o) m) = TmApp (TmUnOp o) (numToTm m)
> numToTm (TyApp (TyApp (BinOp o) m) n) = TmApp (TmApp (TmBinOp o) (numToTm m)) (numToTm n)
> numToTm t = error $ "numToTm: illegal type " ++ show t


> eraseCon :: Constructor -> Contextual Constructor
> eraseCon (c ::: t) = (c :::) <$> eraseToSet t

> eraseAlt :: Alternative () -> Contextual (Alternative ())
> eraseAlt (Alt ps gt) = Alt (erasePatList ps) <$> eraseGuardTerms (unsafeCoerce gt)

> eraseCaseAlt :: CaseAlternative () -> Contextual (CaseAlternative ())
> eraseCaseAlt (CaseAlt p gt) = CaseAlt (erasePat p) <$> eraseGuardTerms(unsafeCoerce gt)

> eraseGuardTerms :: GuardTerms () -> Contextual (GuardTerms ())
> eraseGuardTerms (Unguarded e ds) = Unguarded <$> eraseTm e
>                                    <*> traverse eraseDecl ds
> eraseGuardTerms (Guarded gts ds) = Guarded <$> traverse er gts
>                                    <*> traverse eraseDecl ds
>   where er (g :*: t) = (eraseGuard g :*:) <$> eraseTm t

> eraseGuard :: Guard () -> Guard ()
> eraseGuard (NumGuard ps)  = ExpGuard (foldr1 andExp $ map toTm ps)
>   where
>     andExp a b = TmApp (TmApp (TmCon "(&&)") a) b
>     toTm (P c m n) = TmApp (TmApp (TmCon (toS c)) (numToTm m)) (numToTm n)
>     toTm (_ :=> _) = error "eraseGuard.toTm: implications are not allowed!"
>     toS LE = "(<=)"
>     toS LS = "(<)"
>     toS GE = "(>=)"
>     toS GR = "(>)"
>     toS EL = "(==)"
> eraseGuard g              = g

> erasePat :: Pattern a b -> Pattern () ()
> erasePat (PatVar v)      = PatVar v
> erasePat (PatCon c ps)   = PatCon c (erasePatList ps)
> erasePat PatIgnore       = PatIgnore
> erasePat (PatBrace a 0)  = PatVar a
> erasePat (PatBrace a k)  = PatCon "+" (PatVar a :! PatCon (show k) P0 :! P0)
> erasePat (PatBraceK k)   = PatCon (show k) P0


> erasePatList :: PatternList a b -> PatternList () ()
> erasePatList P0 = P0
> erasePatList (p :! ps) = erasePat p :! erasePatList ps

> eraseDecl :: Declaration () -> Contextual (Declaration ())
> eraseDecl (DataDecl s k cs ds) =
>     case eraseKind k of
>         Just (Ex k') -> do
>             cs <- traverse eraseCon cs
>             return $ DataDecl s k' cs ds
>         Nothing -> error $ "eraseType: failed to erase kind " ++ show k
> eraseDecl (FunDecl x ps) =
>     FunDecl x <$> traverse eraseAlt ps
> eraseDecl (SigDecl x ty) = SigDecl x <$> eraseToSet ty

> eraseProg :: Program -> Contextual Program
> eraseProg = traverse eraseDecl
