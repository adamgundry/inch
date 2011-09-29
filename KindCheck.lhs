> {-# LANGUAGE TypeOperators, GADTs #-}

> module KindCheck where

> import Control.Applicative
> import Control.Monad
> import Data.Traversable

> import BwdFwd
> import Kind
> import Type
> import Num
> import Syntax
> import Context
> import Unify
> import Kit
> import Error
> import PrettyPrinter


> inferKind :: Binder -> Bwd (Ex (Var ())) -> SType -> Contextual t TyKind
> inferKind b g (STyVar x)   = (\ (Ex v) -> TK (TyVar v) (varKind v)) <$> lookupTyVar b g x
> inferKind b g (STyCon c)   = (\ (Ex k) -> TK (TyCon c k) k) <$> lookupTyCon c
> inferKind b g (STyApp f s)  = do
>     TK f' k  <- inferKind b g f
>     case k of
>         k1 :-> k2 -> do
>             TK s' l  <- inferKind b g s
>             hetEq k1 l
>                 (return $ TK (TyApp f' s') k2)
>                 (errKindMismatch (s ::: fogKind l) (fogKind k1))
>             
>         _ -> errKindNotArrow (fogKind k)
> inferKind b g SArr         = return $ TK Arr (KSet :-> KSet :-> KSet)
> inferKind b g (STyInt i)   = return $ TK (TyInt i) KNum
> inferKind b g (SBinOp o)   = return $ TK (BinOp o) (KNum :-> KNum :-> KNum)
> inferKind b g (SBind c a SKNat t)  = do
>     v <- freshVar (UserVar All) a KNum
>     TK ty l <- inferKind b (g :< Ex v) t
>     case l of
>         KSet  -> return $ TK (Bind c a KNum (bindTy v (Qual (P LE 0 (TyVar v)) ty))) KSet
>         _     -> erk "inferKind: forall/pi must have kind *"
> inferKind b g (SBind c a k t)  = case kindKind k of
>     Ex k -> do
>         v <- freshVar (UserVar All) a k
>         TK ty l <- inferKind b (g :< Ex v) t
>         case l of
>             KSet  -> return $ TK (Bind c a k (bindTy v ty)) KSet
>             _     -> erk "inferKind: forall/pi must have kind *"
> inferKind b g (SQual p t) = do
>     p' <- checkPredKind b g p
>     TK t' KSet <- inferKind b g t
>     return $ TK (Qual p' t') KSet

> checkNumKind :: Binder -> Bwd (Ex (Var ())) -> SType -> Contextual t (Type KNum)
> checkNumKind b g t = do
>   TK t k <- inferKind b g t
>   case k of
>     KNum -> return t
>     _ -> erk "checkNumKind: ill-kinded!"

> checkPredKind :: Binder -> Bwd (Ex (Var ())) -> SPredicate -> Contextual t Predicate
> checkPredKind b g = traverse (checkNumKind b g)


