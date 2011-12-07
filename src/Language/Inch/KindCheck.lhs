> {-# LANGUAGE TypeOperators, GADTs #-}

> module Language.Inch.KindCheck where

> import Control.Applicative
> import Data.Traversable

> import Language.Inch.BwdFwd
> import Language.Inch.Kind
> import Language.Inch.Type
> import Language.Inch.Context
> import Language.Inch.Kit
> import Language.Inch.Error

> inferKind :: Binder -> Bwd (Ex (Var ())) -> SType -> Contextual TyKind
> inferKind b g (STyVar x)   = (\ (Ex v) -> TK (TyVar v) (varKind v)) <$> lookupTyVar b g x
> inferKind _ _ (STyCon c)   = (\ (Ex k) -> TK (TyCon c k) k) <$> lookupTyCon c
>                            <|> (\ (Ex t) -> case getTySynKind t of
>                                          k -> TK (TySyn c t) k) <$> lookupTySyn c
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
> inferKind _ _ SArr         = return $ TK Arr (KSet :-> KSet :-> KSet)
> inferKind _ _ (STyInt i)   = return $ TK (TyInt i) KNum
> inferKind _ _ (SUnOp o)    = return $ TK (UnOp o) (KNum :-> KNum)
> inferKind _ _ (SBinOp o)   = return $ TK (BinOp o) (KNum :-> KNum :-> KNum)
> inferKind _ _ (STyComp c)  = return $ TK (TyComp c) (KNum :-> KNum :-> KConstraint)
> inferKind b g (SBind c a SKNat t)  = do
>     v <- freshVar (UserVar All) a KNum
>     ty <- checkKind KSet b (g :< Ex v) t
>     return $ TK (Bind c a KNum (bindTy v (Qual (tyPred LE 0 (TyVar v)) ty))) KSet
> inferKind b g (SBind c a k t)  = case kindKind k of
>     Ex k' -> do
>         v <- freshVar (UserVar All) a k'
>         ty <- checkKind KSet b (g :< Ex v) t
>         return $ TK (Bind c a k' (bindTy v ty)) KSet
> inferKind b g (SQual p t) = do
>     p' <- checkKind KConstraint b g p
>     TK t' KSet <- inferKind b g t
>     return $ TK (Qual p' t') KSet


> checkKind :: Kind k -> Binder -> Bwd (Ex (Var ())) -> SType -> Contextual (Type k)
> checkKind k b g t = do
>   TK t' k' <- inferKind b g t
>   hetEq k k' (return t')
>              (errKindMismatch (fogTy t' ::: fogKind k') (fogKind k))

> checkPredKind :: Binder -> Bwd (Ex (Var ())) -> SPredicate -> Contextual Predicate
> checkPredKind b g = traverse (checkKind KNum b g)