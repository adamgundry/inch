> {-# LANGUAGE TypeOperators, MultiParamTypeClasses, TypeSynonymInstances,
>              GADTs, TypeFamilies, UndecidableInstances #-}

> module Erase where

> import Control.Applicative hiding (Alternative)
> import Control.Monad
> import Data.Traversable
> import Unsafe.Coerce

> import BwdFwd
> import Error
> import Kit
> import Kind
> import Type
> import TyNum
> import Syntax
> import Context
> import TypeCheck


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

> eraseType :: Type k -> Contextual a (Ex Kind, TyKind)
> eraseType (TyVar (FVar a k))    = 
>     case eraseKind k of
>         Just (Ex l) -> return (Ex k, TK (TyVar (FVar a l)) l)
> eraseType (TyCon c k)  =
>     case eraseKind k of
>         Just (Ex l) -> return (Ex k, TK (TyCon c l) l)
> eraseType (TyApp f s)  = do
>         (Ex k, TK f' kf) <- eraseType f
>         case (k, kf) of
>             (k' :-> l, _) | willErase k'  -> return (Ex l, TK f' kf)
>             (k' :-> l, k'' :-> l'')    -> do
>                 (_, TK s' ks) <- eraseType s
>                 hetEq k'' ks (return (Ex l, TK (TyApp f' s') l''))
>                             (erk "Kind mismatch")
> eraseType Arr = return $ (Ex (KSet :-> KSet :-> KSet),
>                           TK Arr (KSet :-> KSet :-> KSet))
> eraseType (Bind Pi x KNum t)   = do
>     (Ex KSet, TK t' KSet) <- eraseType $ unbindTy (error "eraseType: erk") t
>     return (Ex KSet, TK (insertNumArrow t') KSet)
>   where
>     insertNumArrow :: Ty a KSet -> Ty a KSet
>     insertNumArrow (Bind All x k t) = Bind All x k (insertNumArrow t)
>     insertNumArrow t = numTy --> t
> eraseType (Bind All x k t)        = 
>     case eraseKind k of
>         Just (Ex k') -> do
>             an <- fresh SysVar x k Hole
>             (ek, TK t' KSet) <- eraseType (unbindTy an t)
>             return (ek, TK (Bind All x k' (bindTy (FVar (varName an) k') t')) KSet)
>         Nothing -> eraseType $ unbindTy (error "eraseType: erk") t
> eraseType (Qual p t) = eraseType t


> eraseToSet t = do
>     (_, TK t KSet) <- eraseType t
>     return t


> eraseTm :: Term () -> Contextual t (Term ())
> eraseTm (TmVar x)    = pure $ TmVar x
> eraseTm (TmCon c)    = pure $ TmCon c
> eraseTm (TmInt k)    = pure $ TmInt k
> eraseTm (TmApp f s)  = TmApp <$> eraseTm f <*> eraseTm s
> eraseTm (TmBrace n)  = pure $ numToTm n
> eraseTm (Lam x b)    = Lam x <$> eraseTm b
> eraseTm (Let ds t)   = Let <$> traverse eraseDecl ds <*> eraseTm t
> eraseTm (t :? ty)    = do
>     t <- eraseTm t
>     ty <- eraseToSet ty
>     return $ t :? ty

This is a bit of a hack; we really ought to extend the syntax of terms:

> numToTm :: TypeNum -> Term ()
> numToTm (NumVar x)    = TmCon . fogVar $ x
> numToTm (NumConst k)  = TmInt k
> numToTm (m :+: n)     = TmApp (TmApp (TmCon "(+)") (numToTm m)) (numToTm n)
> numToTm (m :*: n)     = TmApp (TmApp (TmCon "(*)") (numToTm m)) (numToTm n)
> numToTm (Neg m)       = TmApp (TmCon "-") (numToTm m)


> eraseCon :: Constructor -> Contextual a Constructor
> eraseCon (c ::: t) = (c :::) <$> eraseToSet t

> eraseAlt :: Alternative () -> Contextual a (Alternative ())
> eraseAlt (Alt ps g t) = Alt (erasePatList ps) (eraseGuard <$> unsafeCoerce g) <$> eraseTm (unsafeCoerce t)

> eraseGuard :: Guard () -> Guard ()
> eraseGuard (NumGuard ps)  = ExpGuard (foldr1 andExp $ map toTm ps)
>   where
>     andExp a b = TmApp (TmApp (TmCon "(&&)") a) b
>     toTm (P c m n) = TmApp (TmApp (TmCon (toS c)) (numToTm m)) (numToTm n)
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

> eraseDecl :: Declaration () -> Contextual a (Declaration ())
> eraseDecl (DataDecl s k cs) =
>     case eraseKind k of
>         Just (Ex k') -> do
>             cs <- traverse eraseCon cs
>             return $ DataDecl s k' cs
> eraseDecl (FunDecl x ps) =
>     FunDecl x <$> traverse eraseAlt ps
> eraseDecl (SigDecl x ty) = SigDecl x <$> eraseToSet ty

> eraseProg :: Program -> Contextual a Program
> eraseProg = traverse eraseDecl
