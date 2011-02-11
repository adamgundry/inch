> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

> module Unify where

> import Control.Applicative
> import Data.Foldable 
> import Prelude hiding (any, mapM_)

> import BwdFwd
> import Syntax
> import Context
> import Num
> import Orphans
> import Kit
> import Error
> import PrettyPrinter

> data Extension = Restore | Replace Suffix

> onTop ::  (TyEntry -> Contextual t Extension)
>             -> Contextual t ()
> onTop f = do
>     c <- getContext
>     case c of
>         _Gamma :< A alphaD -> do
>             putContext _Gamma
>             m <- f alphaD
>             case m of
>                 Replace _Xi  -> modifyContext (<>< _Xi)
>                 Restore      -> modifyContext (:< A alphaD)
>         _Gamma :< xD -> do
>             putContext _Gamma
>             onTop f
>             modifyContext (:< xD)
>         B0 -> fail $ "onTop: ran out of context"

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
>     (<?) :: TyName -> a -> Bool

> instance FV TyName where
>     (<?) = (==)

> instance FV a => FV (Ty a) where
>     alpha <? t = any (alpha <?) t

> instance FV a => FV (TyDef a) where
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


> unify t u = unifyTypes t u `inLoc` (do
>                 t' <- normaliseType t
>                 u' <- normaliseType u
>                 return $ "when unifying\n        " ++ show (prettyFst t')
>                     ++ "\n    and\n        " ++ show (prettyFst u'))

> unifyTypes :: Type -> Type -> Contextual t ()
> -- unifyTypes _ s t | s == t = return ()
> unifyTypes Arr Arr = return ()
> unifyTypes (TyVar alpha) (TyVar beta) = onTop $
>   \ (gamma := d ::: k) -> case
>           (gamma == alpha, gamma == beta, d) of
>           (True,   True,   _)  ->  restore                                 
>           (True,   False,  Hole)      ->  replace ((alpha := Some (var k beta) ::: k) :> F0)
>           (True,   False,  Fixed)     ->  errUnifyFixed alpha (TyVar beta)
>           (False,  True,   Hole)      ->  replace ((beta := Some (var k alpha) ::: k) :> F0)
>           (False,  True,   Fixed)     ->  errUnifyFixed beta (TyVar alpha)

>           (True,   False,  Some tau)  ->  unifyTypes (TyVar beta)   tau       >> restore   
>           (False,  True,   Some tau)  ->  unifyTypes (TyVar alpha)  tau       >> restore   
>           (False,  False,  _)         ->  unifyTypes (TyVar alpha)  (TyVar beta)  >> restore   

> unifyTypes (TyCon c1) (TyCon c2)
>     | c1 == c2   = return ()
>     | otherwise  = fail $ "Mismatched type constructors " ++ c1
>                               ++ " and " ++ c2

> unifyTypes (TyApp f1 s1) (TyApp f2 s2) = unifyTypes f1 f2 >> unifyTypes s1 s2

> unifyTypes (Bind b a k ty) tau = do
>     nm <- fresh a (Hole ::: k)
>     unifyTypes (unbind nm ty) tau

> unifyTypes tau (Bind b a k ty) = do
>     nm <- fresh a (Hole ::: k)
>     unifyTypes tau (unbind nm ty)

> unifyTypes (TyNum m)      (TyNum n)      = unifyNum m n
> unifyTypes (TyNum m)      (TyVar a)      = unifyNum m (NumVar a)
> unifyTypes (TyVar a)      (TyNum n)      = unifyNum (NumVar a) n

> unifyTypes (TyVar alpha)  tau            =  startSolve alpha tau
> unifyTypes tau            (TyVar alpha)  =  startSolve alpha tau
> unifyTypes tau            upsilon = errCannotUnify tau upsilon


> startSolve :: TyName -> Type -> Contextual t ()
> startSolve alpha tau = do
>     (rho, xs) <- rigidHull tau
>     solve alpha (constraintsToSuffix xs) rho
>     solveConstraints xs
>     return ()

> rigidHull :: Type -> Contextual t (Type, Fwd (TyName, TypeNum))
> rigidHull (TyVar a)              = return (TyVar a, F0)
> rigidHull (TyCon c)              = return (TyCon c, F0)
> rigidHull (TyApp f s)            = do  (f',      xs  )  <- rigidHull f
>                                        (s',  ys  )  <- rigidHull s
>                                        return (TyApp f' s', xs <+> ys)
> rigidHull Arr = return (Arr, F0)
> rigidHull (TyNum d)          = do  n <- freshName
>                                    let beta = ("_i", n)
>                                    return (TyNum (NumVar beta), (beta, d) :> F0)
> rigidHull (Bind b x k t) = return (Bind b x k t, F0)

> constraintsToSuffix :: Fwd (TyName, TypeNum) -> Suffix
> constraintsToSuffix = fmap ((:= Hole ::: KindNum) . fst)

> solveConstraints :: Fwd (TyName, TypeNum) -> Contextual t ()
> solveConstraints = mapM_ (uncurry $ unifyNum . NumVar)


> solve :: TyName -> Suffix -> Type -> Contextual t ()
> solve alpha _Xi tau = onTop $
>   \ (gamma := d ::: k) -> let occurs = gamma <? tau || gamma <? _Xi in case
>     (gamma == alpha, occurs, d) of
>     (True,   True,   _)             ->  fail "Occurrence detected!"
>     (True,   False,  Hole)          ->  replace (_Xi <+> ((alpha := Some tau ::: k) :> F0))
>     (True,   False,  Some upsilon)  ->  modifyContext (<>< _Xi)
>                                         >>  unifyTypes upsilon tau
>                                         >>  restore
>     (True,   False,  Fixed)         ->  errUnifyFixed alpha tau
>     (False,  True,   Hole)          ->  solve alpha ((gamma := d ::: k) :> _Xi) tau
>                                         >>  replace F0   
>     (False,  True,   Some upsilon)  ->  do
>         (upsilon', xs) <- rigidHull upsilon
>         solve alpha (constraintsToSuffix xs <+> ((gamma := Some upsilon' ::: k) :> _Xi)) tau
>         solveConstraints xs
>         replace F0
>     (False,  False,  _)             ->  solve alpha _Xi tau
>                                         >>  restore




> type NormNum a = GExp () a
> type NormalNum = NormNum TyName

> unifyNum :: TypeNum -> TypeNum -> Contextual t ()
> unifyNum (NumConst 0) n = unifyZero Nothing =<< normaliseNum n
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

> lookupNormNumVar :: TyName -> Contextual t NormalNum
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
> reifyNum = foldGExp (\ k n m -> NumConst k * NumVar n + m) NumConst

> unifyZero :: Maybe TyName -> NormalNum -> Contextual t ()
> unifyZero _Psi e
>   | isIdentity e  = return ()
>   | isConstant e  = errCannotUnify (numToType e) (numToType (normalConst 0))
>   | otherwise     = onTopNum $
>     \ (alpha := d ::: KindNum) ->
>     case lookupVariable alpha e of
>         Nothing  -> unifyZero _Psi e >> restore
>         Just n   -> case d of
>             Some x   -> do
>                           modifyContext (<><| _Psi)
>                           x' <- typeToNum x
>                           unifyZero Nothing (substGExp (alpha, n) x' e)
>                           restore
>             Hole  | n `dividesCoeffs` e -> do
>                           modifyContext (<><| _Psi)
>                           replace $ (alpha := Some (numToType (pivot (alpha, n) e)) ::: KindNum) :> F0
>                      | (alpha, n) `notMaxCoeff` e -> do
>                           modifyContext (<><| _Psi)
>                           (p, beta) <- insertFreshVar $ pivot (alpha, n) e
>                           unifyZero (Just beta) $ substGExp (alpha, n) p e
>                           replace $ (alpha := Some (numToType p) ::: KindNum) :> F0
>                      | numVariables e > 1 -> do
>                           demandNothing _Psi
>                           unifyZero (Just alpha) e
>                           replace F0
>                      | otherwise -> fail "No way!"
>             Fixed -> errUnifyNumFixed alpha (simplifyNum $ reifyNum e)
>   where
>     _Gamma <><| Nothing     = _Gamma
>     _Gamma <><| Just alpha  = _Gamma :< A (alpha := Hole ::: KindNum)
>
>     demandNothing Nothing   = return ()
>     demandNothing (Just _)  = error "demandNothing: invariants violated!"


We can insert a fresh variable into a unit thus:

> insertFreshVar :: NormalNum -> Contextual t (NormalNum, TyName)
> insertFreshVar d = do
>     n <- freshName
>     let beta = ("beta", n)
>     return (d +~ embedVar beta, beta)