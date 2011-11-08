> {-# LANGUAGE TypeOperators, GADTs #-}

> module Language.Inch.KindCheck where

> import Control.Applicative
> import Data.Set (Set)
> import qualified Data.Set as Set
> import Data.Traversable

> import Language.Inch.BwdFwd
> import Language.Inch.Kind
> import Language.Inch.Type
> import Language.Inch.Context
> import Language.Inch.Kit
> import Language.Inch.Error


> wrapForall :: [String] -> SType -> SType
> wrapForall _ t@(SBind All _ _ _) = t
> wrapForall xs t = Set.fold (\ x y -> SBind All x SKSet y) t (collectUnbound xs t)
>   where
>     collectUnbound :: [String] -> SType -> Set String
>     collectUnbound bs (STyVar s) | s `elem` bs  = Set.empty
>                                  | otherwise    = Set.singleton s
>     collectUnbound _ (STyCon _)       = Set.empty
>     collectUnbound bs (STyApp f s)     = collectUnbound bs f `Set.union` collectUnbound bs s
>     collectUnbound _ SArr             = Set.empty
>     collectUnbound _ (STyInt _)       = Set.empty
>     collectUnbound _ (SUnOp _)        = Set.empty
>     collectUnbound _ (SBinOp _)       = Set.empty
>     collectUnbound _ (STyComp _)       = Set.empty
>     collectUnbound bs (SBind _ b _ u)  = collectUnbound (b:bs) u
>     collectUnbound bs (SQual p u)      = collectUnbound bs p `Set.union` collectUnbound bs u


> inferKind :: Binder -> Bwd (Ex (Var ())) -> SType -> Contextual TyKind
> inferKind b g (STyVar x)   = (\ (Ex v) -> TK (TyVar v) (varKind v)) <$> lookupTyVar b g x
> inferKind _ _ (STyCon c)   = (\ (Ex k) -> TK (TyCon c k) k) <$> lookupTyCon c
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
>     ty <- checkKindSet b (g :< Ex v) t
>     return $ TK (Bind c a KNum (bindTy v (Qual (tyPred LE 0 (TyVar v)) ty))) KSet
> inferKind b g (SBind c a k t)  = case kindKind k of
>     Ex k' -> do
>         v <- freshVar (UserVar All) a k'
>         ty <- checkKindSet b (g :< Ex v) t
>         return $ TK (Bind c a k' (bindTy v ty)) KSet
> inferKind b g (SQual p t) = do
>     p' <- checkConstraintKind b g p
>     TK t' KSet <- inferKind b g t
>     return $ TK (Qual p' t') KSet

> checkNumKind :: Binder -> Bwd (Ex (Var ())) -> SType -> Contextual (Type KNum)
> checkNumKind b g t = do
>   TK t' k <- inferKind b g t
>   case k of
>     KNum  -> return t'
>     _     -> errKindMismatch (fogTy t' ::: fogKind k) SKNum

> checkConstraintKind :: Binder -> Bwd (Ex (Var ())) -> SType -> Contextual (Type KConstraint)
> checkConstraintKind b g t = do
>   TK t' k <- inferKind b g t
>   case k of
>     KConstraint  -> return t'
>     _            -> errKindMismatch (fogTy t' ::: fogKind k) SKConstraint


> checkPredKind :: Binder -> Bwd (Ex (Var ())) -> SPredicate -> Contextual Predicate
> checkPredKind b g = traverse (checkNumKind b g)



> checkKindSet :: Binder -> Bwd (Ex (Var ())) -> SType -> Contextual (Type KSet)
> checkKindSet b g t = do
>     TK t' k <- inferKind b g t
>     case k of
>         KSet  -> return t'
>         _     -> errKindNotSet (fogKind k)