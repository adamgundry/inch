> {-# LANGUAGE TypeOperators #-}

> module KindCheck where

> import Control.Applicative
> import Control.Monad

> import BwdFwd
> import TyNum
> import Type
> import Num
> import Syntax
> import Context
> import Unify
> import Orphans
> import Kit
> import Error
> import PrettyPrinter


> inferKind :: Bwd (TyName ::: Kind) -> SType -> Contextual t (Type ::: Kind)
> inferKind g (TyVar _ a)  = (\ (b ::: k) -> TyVar k b ::: k) <$> lookupTyVar g a
> inferKind g (TyCon c)    = (TyCon c :::) <$> lookupTyCon c
> inferKind g (TyApp f s)  = do
>     f' ::: k  <- inferKind g f
>     case k of
>         KindArr k1 k2 -> do
>             s' ::: l  <- inferKind g s
>             unless (k1 == l) $ errKindMismatch (s' ::: l) k1
>             return $ TyApp f' s' ::: k2
>         _ -> errKindNotArrow k
> inferKind g (TyB b)         = return $ TyB b ::: builtinKind b
> inferKind g (TyNum n)       = (\ n -> TyNum n ::: KindNum) <$> checkNumKind g n
> inferKind g (Bind b a k t)  = do
>     n <- freshName
>     ty ::: l <- inferKind (g :< ((a, n) ::: k)) (unbind a t)
>     return $ Bind b a k (bind (a, n) ty) ::: l
> inferKind g (Qual p t) = do
>     p' <- checkPredKind g p
>     t' ::: k <- inferKind g t
>     return (Qual p' t' ::: k)

> checkNumKind :: Bwd (TyName ::: Kind) -> TyNum String -> Contextual t TypeNum
> checkNumKind g (NumConst k) = return $ NumConst k
> checkNumKind g (NumVar a) = lookupNumVar g a
> checkNumKind g (m :+: n) = (:+:) <$> checkNumKind g m <*> checkNumKind g n
> checkNumKind g (m :*: n) = (:*:) <$> checkNumKind g m <*> checkNumKind g n
> checkNumKind g (Neg n) = Neg <$> checkNumKind g n

> checkPredKind :: Bwd (TyName ::: Kind) -> Pred String -> Contextual t Predicate
> checkPredKind g (n :<=: m) = (:<=:) <$> checkNumKind g n <*> checkNumKind g m
> checkPredKind g (n :==: m) = (:==:) <$> checkNumKind g n <*> checkNumKind g m


> scopeCheckTypes :: STerm -> Contextual () Term
> scopeCheckTypes = trav3 (checkNumKind B0) (\ t -> tmOf <$> inferKind B0 t) pure