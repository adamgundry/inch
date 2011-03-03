> {-# LANGUAGE TypeOperators, MultiParamTypeClasses, TypeSynonymInstances #-}

> module Erase where

> import Control.Applicative
> import Control.Monad
> import Data.Traversable

> import BwdFwd
> import Kit
> import Type
> import TyNum
> import Syntax
> import Context
> import TypeCheck


> eraseKind :: (Applicative f, Monad f) => Kind -> f Kind
> eraseKind Set                  = pure Set
> eraseKind KindNum              = fail "Cannot erase kind *"
> eraseKind (KindArr KindNum l)  = eraseKind l
> eraseKind (KindArr k l)        = KindArr <$> eraseKind k <*> eraseKind l


> eraseType :: Type -> Contextual a (Type ::: Kind)
> eraseType (TyVar k a)  = return $ TyVar k a ::: k
> eraseType (TyCon c)    = (TyCon c :::) <$> lookupTyCon c
> eraseType (TyApp f s)  = do
>         (f' ::: kf) <- eraseType f
>         case kf of
>             KindArr KindNum l        -> return $ f' ::: l
>             KindArr k' l -> do
>                 (s' ::: ks) <- eraseType s
>                 unless (k' == ks) $ fail "Kind mismatch"
>                 return $ TyApp f' s' ::: l
> eraseType (TyB b) = return $ TyB b ::: builtinKind b
> eraseType (Bind Pi x KindNum t)   = do
>     t' ::: Set <- eraseType $ unbind (error "eraseType: erk") t
>     return (TyB NumTy --> t' ::: Set)
> eraseType (Bind All x KindNum t)  = eraseType $ unbind (error "eraseType: erk") t
> eraseType (Bind b x k t)        = do
>     an <- fresh x (Hole ::: k)
>     k' <- eraseKind k
>     t' ::: kt <- eraseType (unbind an t)
>     return $ Bind b x k' (bind an t') ::: kt
> eraseType (Qual p t) = eraseType t


> eraseTm :: Tm Kind TyName x -> Contextual t (Tm Kind TyName x)
> eraseTm (TmVar x)    = pure $ TmVar x
> eraseTm (TmCon c)    = pure $ TmCon c
> eraseTm (TmApp f s)  = TmApp <$> eraseTm f <*> eraseTm s
> eraseTm (TmBrace n)  = pure $ numToTm n
> eraseTm (Lam x b)    = Lam x <$> eraseTm b
> eraseTm (t :? ty)    = (:?) <$> eraseTm t <*> (tmOf <$> eraseType ty)

This is a bit of a hack; we really ought to extend the syntax of terms:

> numToTm :: TypeNum -> Tm Kind TyName x
> numToTm (NumVar x)    = TmCon (fst x)
> numToTm (NumConst k)  = TmCon (show k)
> numToTm (m :+: n)     = TmApp (TmApp (TmCon "(+)") (numToTm m)) (numToTm n)
> numToTm (m :*: n)     = TmApp (TmApp (TmCon "(*)") (numToTm m)) (numToTm n)
> numToTm (Neg m)       = TmApp (TmCon "-") (numToTm m)


> eraseCon :: Constructor -> Contextual a Constructor
> eraseCon (c ::: t) = ((c :::) . tmOf) <$> eraseType t

> erasePat :: Pattern -> Contextual a Pattern
> erasePat (Pat ps Trivial t) = Pat (map erasePatTm ps) Trivial <$> eraseTm t

> erasePatTm :: PatternTerm -> PatternTerm
> erasePatTm (PatBrace Nothing k)   = PatCon (show k) []
> erasePatTm (PatBrace (Just a) 0)  = PatVar a
> erasePatTm (PatBrace (Just a) k)  = PatCon "+" [PatVar a, PatCon (show k) []]
> erasePatTm (PatCon c ps) = PatCon c (map erasePatTm ps)
> erasePatTm t = t

> eraseDecl :: Declaration -> Contextual a Declaration
> eraseDecl (DD (DataDecl s k cs)) =
>     DD <$> (DataDecl s <$> eraseKind k <*> traverse eraseCon cs)
> eraseDecl (FD (FunDecl x mt ps)) =
>     FD <$> (FunDecl x <$> traverse (\ t -> tmOf <$> eraseType t) mt
>                       <*> traverse erasePat ps)

> eraseProg :: Program -> Contextual a Program
> eraseProg = traverse eraseDecl