> {-# LANGUAGE TypeOperators, MultiParamTypeClasses, TypeSynonymInstances #-}

> module Erase where

> import Control.Applicative
> import Control.Monad
> import Data.Traversable

> import BwdFwd
> import Error
> import Kit
> import Type
> import TyNum
> import Syntax
> import Context
> import TypeCheck


> eraseKind :: Kind -> Contextual a Kind
> eraseKind Set                  = pure Set
> eraseKind KindNum              = erk "Cannot erase kind *"
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
>                 unless (k' == ks) $ erk "Kind mismatch"
>                 return $ TyApp f' s' ::: l
> eraseType (TyB b) = return $ TyB b ::: builtinKind b
> eraseType (Bind Pi x KindNum t)   = do
>     t' ::: Set <- eraseType $ unbind (error "eraseType: erk") t
>     return (insertNumArrow t' ::: Set)
>   where
>     insertNumArrow :: Ty k a -> Ty k a
>     insertNumArrow (Bind All x k t) = Bind All x k (insertNumArrow t)
>     insertNumArrow t = TyB NumTy --> t
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
> eraseTm (TmInt k)    = pure $ TmInt k
> eraseTm (TmApp f s)  = TmApp <$> eraseTm f <*> eraseTm s
> eraseTm (TmBrace n)  = pure $ numToTm n
> eraseTm (Lam x b)    = Lam x <$> eraseTm b
> eraseTm (Let ds t)   = Let <$> traverse eraseFunDecl ds <*> eraseTm t
> eraseTm (t :? ty)    = (:?) <$> eraseTm t <*> (tmOf <$> eraseType ty)

This is a bit of a hack; we really ought to extend the syntax of terms:

> numToTm :: TypeNum -> Tm Kind TyName x
> numToTm (NumVar x)    = TmCon (fst x)
> numToTm (NumConst k)  = TmInt k
> numToTm (m :+: n)     = TmApp (TmApp (TmCon "(+)") (numToTm m)) (numToTm n)
> numToTm (m :*: n)     = TmApp (TmApp (TmCon "(*)") (numToTm m)) (numToTm n)
> numToTm (Neg m)       = TmApp (TmCon "-") (numToTm m)


> eraseCon :: Constructor -> Contextual a Constructor
> eraseCon (c ::: t) = ((c :::) . tmOf) <$> eraseType t

> erasePat :: Pat Kind TyName x -> Contextual a (Pat Kind TyName x)
> erasePat (Pat ps g t) = Pat (map erasePatTm ps) (eraseGuard <$> g) <$> eraseTm t

> eraseGuard :: Grd Kind TyName x -> Grd Kind TyName x
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

> erasePatTm :: PatTerm Kind TyName x -> PatTerm Kind TyName x
> erasePatTm (PatBrace Nothing k)   = PatCon (show k) []
> erasePatTm (PatBrace (Just a) 0)  = PatVar a
> erasePatTm (PatBrace (Just a) k)  = PatCon "+" [PatVar a, PatCon (show k) []]
> erasePatTm (PatCon c ps) = PatCon c (map erasePatTm ps)
> erasePatTm t = t

> eraseFunDecl :: FunDecl Kind TyName x -> Contextual t (FunDecl Kind TyName x)
> eraseFunDecl (FunDecl x mt ps) =
>     FunDecl x <$> traverse (\ t -> tmOf <$> eraseType t) mt
>               <*> traverse erasePat ps

> eraseDecl :: Declaration -> Contextual a Declaration
> eraseDecl (DD (DataDecl s k cs)) =
>     DD <$> (DataDecl s <$> eraseKind k <*> traverse eraseCon cs)
> eraseDecl (FD f) = FD <$> eraseFunDecl f

> eraseProg :: Program -> Contextual a Program
> eraseProg = traverse eraseDecl