> {-# LANGUAGE TypeOperators, MultiParamTypeClasses, TypeSynonymInstances,
>              GADTs, TypeFamilies, UndecidableInstances #-}

> module Erase where

> import Control.Applicative
> import Control.Monad
> import Data.Traversable

> import BwdFwd
> import Error
> import Kit
> import Kind
> import Type
> import TyNum
> import Syntax
> import Context
> import TypeCheck


> eraseKind :: Kind k -> Contextual a (Ex Kind)
> eraseKind KSet          = return $ Ex KSet
> eraseKind KNum          = return $ Ex KNum
> eraseKind (k :-> l)  = do
>     Ex k' <- eraseKind k
>     Ex l' <- eraseKind l
>     case k' of
>         KNum  -> return $ Ex l'
>         _     -> return $ Ex $ k' :-> l'


> eraseType :: Type k -> Contextual a (Ex Kind, TyKind)
> eraseType (TyVar (FVar a k))    = do
>     Ex l <- eraseKind k
>     return (Ex k, TK (TyVar (FVar a l)) l)
> eraseType (TyCon c k)  = do
>     Ex l <- eraseKind k
>     return (Ex k, TK (TyCon c l) l)
> eraseType (TyApp f s)  = do
>         (Ex k, TK f' kf) <- eraseType f
>         case (k, kf) of
>             (KNum :-> l, _)  -> return (Ex l, TK f' kf)
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
> eraseType (Bind All x KNum t)  = eraseType $ unbindTy (error "eraseType: erk") t
> eraseType (Bind b x k t)        = do
>     an <- fresh SysVar x k Hole
>     Ex k' <- eraseKind k
>     (ek, TK t' kt) <- eraseType (unbindTy an t)
>     return (ek, TK (Bind b x k' (bindTy (FVar (varName an) k') t')) kt)
> eraseType (Qual p t) = eraseType t


> eraseToSet t = do
>     (_, TK t KSet) <- eraseType t
>     return t


> eraseTm :: Term -> Contextual t Term
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

> numToTm :: TypeNum -> Term
> numToTm (NumVar x)    = TmCon . fogVar $ x
> numToTm (NumConst k)  = TmInt k
> numToTm (m :+: n)     = TmApp (TmApp (TmCon "(+)") (numToTm m)) (numToTm n)
> numToTm (m :*: n)     = TmApp (TmApp (TmCon "(*)") (numToTm m)) (numToTm n)
> numToTm (Neg m)       = TmApp (TmCon "-") (numToTm m)


> eraseCon :: Constructor -> Contextual a Constructor
> eraseCon (c ::: t) = (c :::) <$> eraseToSet t

> erasePat :: Pattern -> Contextual a Pattern
> erasePat (Pat ps g t) = Pat (map erasePatTm ps) (eraseGuard <$> g) <$> eraseTm t

> eraseGuard :: Guard -> Guard
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

> erasePatTm :: PatternTerm -> PatternTerm
> erasePatTm (PatBrace Nothing k)   = PatCon (show k) []
> erasePatTm (PatBrace (Just a) 0)  = PatVar a
> erasePatTm (PatBrace (Just a) k)  = PatCon "+" [PatVar a, PatCon (show k) []]
> erasePatTm (PatCon c ps) = PatCon c (map erasePatTm ps)
> erasePatTm t = t

> eraseDecl :: Declaration -> Contextual a Declaration
> eraseDecl (DataDecl s k cs) = do
>     Ex k <- eraseKind k
>     cs <- traverse eraseCon cs
>     return $ DataDecl s k cs
> eraseDecl (FunDecl x ps) =
>     FunDecl x <$> traverse erasePat ps
> eraseDecl (SigDecl x ty) = SigDecl x <$> eraseToSet ty

> eraseProg :: Program -> Contextual a Program
> eraseProg = traverse eraseDecl
