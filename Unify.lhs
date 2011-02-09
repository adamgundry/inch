> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

> module Unify where

> import Control.Applicative
> import Data.Foldable 
> import Prelude hiding (any)

> import BwdFwd
> import Syntax
> import Context
> import Num
> import Orphans


> data Extension = Restore | Replace Suffix

> onTop ::  (TyEntry -> Contextual t Extension)
>             -> Contextual t ()
> onTop f = do
>     _Gamma :< vD <- getContext
>     putContext _Gamma
>     case vD of
>         A alphaD  -> do  m <- f alphaD
>                          case m of
>                              Replace _Xi  -> modifyContext (<>< _Xi)
>                              Restore      -> modifyContext (:< vD)
>         _         -> onTop f >> modifyContext (:< vD)

> onTopNum ::  (TyEntry -> Contextual t Extension)
>             -> Contextual t ()
> onTopNum f = do
>     _Gamma :< vD <- getContext
>     putContext _Gamma
>     case vD of
>         A (a := d ::: KindNum) -> do
>             m <- f (a := d ::: KindNum)
>             case m of
>                 Replace _Xi  -> modifyContext (<>< _Xi)
>                 Restore      -> modifyContext (:< vD)
>         _ -> onTopNum f >> modifyContext (:< vD)

> restore :: Contextual t Extension
> restore = return Restore

> replace :: Suffix -> Contextual t Extension
> replace = return . Replace


> class FV a where
>     (<?) :: Name -> a -> Bool

> instance FV Name where
>     (<?) = (==)

> instance FV a => FV (Ty a) where
>     alpha <? t = any (alpha <?) t

> instance FV a => FV (Maybe a) where
>     alpha <? t = any (alpha <?) t

> instance FV Suffix where
>     alpha <? t = any (alpha <?) t

> instance FV TyEntry where
>     alpha <? (a := d ::: k) = alpha <? a || alpha <? d


Invariant: if a definition |a := Just d ::: KindNat| is in the
context, then |d| must be of the form |TyNum n| for some |n|.

> var :: Kind -> a -> Ty a
> var KindNum  = TyNum . NumVar
> var _        = TyVar


> unify :: Type -> Type -> Contextual t ()
> unify Arr Arr = return ()
> unify (TyVar alpha)        (TyVar beta)                 = onTop $
>   \ (gamma := d ::: k) -> case
>           (gamma == alpha,  gamma == beta,  d         ) of
>           (True,            True,           _         )  ->  restore                                 
>           (True,            False,          Nothing   )  ->  replace ((alpha := Just (var k beta) ::: k) :> F0)
>           (False,           True,           Nothing   )  ->  replace ((beta := Just (var k alpha) ::: k) :> F0)
>           (True,            False,          Just tau  )  ->  unify (TyVar beta)   tau       >> restore   
>           (False,           True,           Just tau  )  ->  unify (TyVar alpha)  tau       >> restore   
>           (False,           False,          _         )  ->  unify (TyVar alpha)  (TyVar beta)  >> restore   

> unify (TyCon c1) (TyCon c2)
>     | c1 == c2   = return ()
>     | otherwise  = fail $ "Mismatched type constructors " ++ fst c1
>                               ++ " and " ++ fst c2

> unify (TyApp f1 s1) (TyApp f2 s2) = unify f1 f2 >> unify s1 s2

> unify (Bind b a k ty) tau = do
>     nm <- fresh a (Nothing ::: k)
>     unify (unbind nm ty) tau

> unify tau (Bind b a k ty) = do
>     nm <- fresh a (Nothing ::: k)
>     unify tau (unbind nm ty)

> unify (TyNum m)      (TyNum n)      = unifyNum m n

> unify (TyVar alpha)  tau            =  solve alpha F0 tau
> unify tau            (TyVar alpha)  =  solve alpha F0 tau
> unify tau            upsilon        =  fail $ "Could not unify " ++ show tau ++ " and " ++ show upsilon

> solve :: Name -> Suffix -> Type -> Contextual t ()
> solve alpha _Xi tau = onTop $
>   \ (gamma := d ::: k) -> let occurs = gamma <? tau || gamma <? _Xi in case
>     (gamma == alpha,  occurs,  d             ) of
>     (True,            True,    _             )  ->  fail "Occurrence detected!"
>     (True,            False,   Nothing       )  ->  replace (_Xi <+> ((alpha := Just tau ::: k) :> F0))
>     (True,            False,   Just upsilon  )  ->  modifyContext (<>< _Xi)
>                                                 >>  unify upsilon tau
>                                                 >>  restore
>     (False,           True,    _             )  ->  solve alpha ((gamma := d ::: k) :> _Xi) tau
>                                                 >>  replace F0   
>     (False,           False,   _             )  ->  solve alpha _Xi tau
>                                                 >>  restore




> type NormNum a = GExp () a
> type NormalNum = NormNum Name

> unifyNum :: TypeNum -> TypeNum -> Contextual t ()
> unifyNum m n = unifyZero Nothing =<< normaliseNum (m - n)

> normaliseNum :: TypeNum -> Contextual t NormalNum
> normaliseNum (NumConst k)  = return $ normalConst k
> normaliseNum (NumVar a)    = return $ embedVar a
> normaliseNum (m :+: n)     = (+~) <$> normaliseNum m <*> normaliseNum n
> normaliseNum (m :*: n)     = do
>     m'  <- normaliseNum m
>     n'  <- normaliseNum n
>     case (getConstant m', getConstant n') of
>         (Just i,   Just j)   -> return $ normalConst (i * j)
>         (Just i,   Nothing)  -> return $ i *~ n'
>         (Nothing,  Just j)   -> return $ j *~ m'
>         (Nothing,  Nothing)  -> fail "Non-linear numeric expression"
> normaliseNum (Neg n)       = negateGExp <$> normaliseNum n

> normalConst k = mkGExp [] [((), k)]

> typeToNum :: Type -> Contextual t NormalNum
> typeToNum (TyNum n) = normaliseNum n
> typeToNum (TyVar a) = lookupNormNumVar a
> typeToNum t = fail $ "Bad type in numeric constraint: " ++ show t

> lookupNormNumVar :: Name -> Contextual t NormalNum
> lookupNormNumVar a = getContext >>= seek
>   where
>     seek B0 = fail $ "Missing numeric variable " ++ show a
>     seek (g :< A (b := _ ::: k))
>         | a == b && k == KindNum = return $ embedVar a
>         | a == b = fail $ "Type variable " ++ show a ++ " is not numeric"
>     seek (g :< _) = seek g


> numToType :: NormalNum -> Type
> numToType  = TyNum . reifyNum

> reifyNum :: NormalNum -> TypeNum
> reifyNum = foldGExp (\ k n m -> (NumConst k) * (NumVar n) + m) NumConst

> unifyZero :: Maybe Name -> NormalNum -> Contextual t ()
> unifyZero _Psi e
>   | isIdentity e  = return ()
>   | isConstant e  = fail "Unit mismatch!"
>   | otherwise     = onTopNum $
>     \ (alpha := d ::: KindNum) ->
>     case lookupVariable alpha e of
>         Nothing  -> unifyZero _Psi e >> restore
>         Just n   -> case d of
>             Just x   -> do
>                           modifyContext (<><| _Psi)
>                           x' <- typeToNum x
>                           unifyZero Nothing (substGExp (alpha, n) x' e)
>                           restore
>             Nothing  | n `dividesCoeffs` e -> do
>                           modifyContext (<><| _Psi)
>                           replace $ (alpha := Just (numToType (pivot (alpha, n) e)) ::: KindNum) :> F0
>                      | (alpha, n) `notMaxCoeff` e -> do
>                           modifyContext (<><| _Psi)
>                           (p, beta) <- insertFreshVar $ pivot (alpha, n) e
>                           unifyZero (Just beta) $ substGExp (alpha, n) p e
>                           replace $ (alpha := Just (numToType p) ::: KindNum) :> F0
>                      | numVariables e > 1 -> do
>                           demandNothing _Psi
>                           unifyZero (Just alpha) e
>                           replace F0
>                      | otherwise -> fail "No way!"
>   where
>     _Gamma <><| Nothing     = _Gamma
>     _Gamma <><| Just alpha  = _Gamma :< A (alpha := Nothing ::: KindNum)
>
>     demandNothing Nothing   = return ()
>     demandNothing (Just _)  = error "demandNothing: invariants violated!"


We can insert a fresh variable into a unit thus:

> insertFreshVar :: NormalNum -> Contextual t (NormalNum, Name)
> insertFreshVar d = do
>     n <- freshName
>     let beta = ("beta", n)
>     return (d +~ embedVar beta, beta)