> {-# LANGUAGE TypeOperators, MultiParamTypeClasses, TypeSynonymInstances #-}

> module Erase where

> import Control.Applicative
> import Control.Monad
> import Data.Traversable

> import BwdFwd
> import Kit
> import Type
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
> eraseType Arr = return $ Arr ::: Set ---> Set ---> Set
> eraseType (Bind b x KindNum t)  = eraseType $ unbind (error "eraseType: erk") t
> eraseType (Bind b x k t)        = do
>     an <- fresh x (Hole ::: k)
>     k' <- eraseKind k
>     t' ::: kt <- eraseType (unbind an t)
>     return $ Bind b x k' (bind an t') ::: kt
> eraseType (Qual p t) = eraseType t


> eraseTerm :: Term -> Contextual a (Term ::: Type)
> eraseTerm (TmVar x)    = (TmVar x :::) <$> undefined
> eraseTerm (TmCon c)    = (TmCon c :::) <$> undefined
> eraseTerm (TmApp f s)  = undefined


> eraseCon :: Constructor -> Contextual a Constructor
> eraseCon (c ::: t) = ((c :::) . tmOf) <$> eraseType t

> erasePat :: Pattern -> Contextual a Pattern
> erasePat = return

> eraseDecl :: Declaration -> Contextual a Declaration
> eraseDecl (DD (DataDecl s k cs)) =
>     DD <$> (DataDecl s <$> eraseKind k <*> traverse eraseCon cs)
> eraseDecl (FD (FunDecl x mt ps)) =
>     FD <$> (FunDecl x <$> traverse (\ t -> tmOf <$> eraseType t) mt
>                       <*> traverse erasePat ps)

> eraseProg :: Program -> Contextual a Program
> eraseProg = traverse eraseDecl