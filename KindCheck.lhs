> {-# LANGUAGE TypeOperators, GADTs #-}

> module KindCheck where

> import Control.Applicative
> import Control.Monad
> import Data.Traversable

> import BwdFwd
> import TyNum
> import Kind
> import Type
> import Num
> import Syntax
> import Context
> import Unify
> import Kit
> import Error
> import PrettyPrinter


> inferKind :: Bwd (Ex (Var ())) -> SType -> Contextual t TyKind
> inferKind g (STyVar x)   = (\ (Ex v) -> TK (TyVar v) (varKind v)) <$> lookupTyVar g x
> inferKind g (STyCon c)   = (\ (Ex k) -> TK (TyCon c k) k) <$> lookupTyCon c
> inferKind g (STyApp f s)  = do
>     TK f' k  <- inferKind g f
>     case k of
>         k1 :-> k2 -> do
>             TK s' l  <- inferKind g s
>             hetEq k1 l
>                 (return $ TK (TyApp f' s') k2)
>                 (errKindMismatch (s ::: fogKind l) (fogKind k1))
>             
>         _ -> errKindNotArrow (fogKind k)
> inferKind g SArr         = return $ TK Arr (KSet :-> KSet :-> KSet)
> inferKind g (STyNum n)       = (\ n -> TK (TyNum n) KNum) <$> checkNumKind g n
> inferKind g (SBind b a k t)  = case kindKind k of
>     Ex k -> do
>         v <- freshVar UserVar a k
>         TK ty l <- inferKind (g :< Ex v) t
>         return $ TK (Bind b a k (bindTy v ty)) l
> inferKind g (SQual p t) = do
>     p' <- checkPredKind g p
>     TK t' k <- inferKind g t
>     return $ TK (Qual p' t') k

> checkNumKind :: Bwd (Ex (Var ())) -> TyNum String -> Contextual t TypeNum
> checkNumKind g = traverse (lookupNumVar g)

> checkPredKind :: Bwd (Ex (Var ())) -> Pred String -> Contextual t Predicate
> checkPredKind g = travPred (checkNumKind g)


