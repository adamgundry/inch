> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

> module Unify where

> import Control.Applicative
> import Control.Monad hiding (mapM_)
> import Data.Foldable 
> import Data.Maybe
> import Prelude hiding (any, mapM_)

> import BwdFwd
> import TyNum
> import Type
> import Syntax
> import Context
> import Num
> import Orphans
> import Kit
> import Error
> import PrettyPrinter
> import PrettyContext

> data Extension = Restore | Replace Suffix

> onTop ::  (TyEntry -> Contextual t Extension)
>             -> Contextual t ()
> onTop f = do
>     c <- getContext
>     case c of
>         _Gamma :< A alphaD -> do
>             putContext _Gamma
>             ext (A alphaD) =<< f alphaD
>         _Gamma :< xD -> do
>             putContext _Gamma
>             onTop f
>             modifyContext (:< xD)
>         B0 -> fail $ "onTop: ran out of context"

> onTopNum ::  (NormalPredicate, Contextual t ()) ->
>                  (NormalPredicate -> Contextual t ()) ->
>                  (TyEntry -> Contextual t Extension) ->
>                  Contextual t ()
> onTopNum (p, m) h f = do
>   g <- getContext
>   case g of
>     _Gamma :< xD -> do  
>       putContext _Gamma
>       case xD of
>         A (a := d ::: KindNum) -> ext xD =<< f (a := d ::: KindNum)
>         Layer pt@(PatternTop _ _ (_:_) cs) -> do
>             modifyContext (:< Layer (pt{ptConstraints = p : cs}))
>             m
>         Constraint c -> h c >> modifyContext (:< xD)
>         _ -> onTopNum (p, m) h f >> modifyContext (:< xD)
>     B0 -> inLocation ("when solving " ++ render p) $
>               fail $ "onTopNum: ran out of context"

> restore :: Contextual t Extension
> restore = return Restore

> replace :: Suffix -> Contextual t Extension
> replace = return . Replace

> ext :: Entry -> Extension -> Contextual t ()
> ext xD (Replace _Xi)  = modifyContext (<>< _Xi)
> ext xD Restore        = modifyContext (:< xD)

> class FV a where
>     (<?) :: TyName -> a -> Bool

> instance FV TyName where
>     (<?) = (==)

> instance FV a => FV (Ty k a) where
>     alpha <? t = any (alpha <?) t

> instance FV a => FV (TyDef a) where
>     alpha <? t = any (alpha <?) t

> instance FV Suffix where
>     alpha <? t = any (alpha <?) t

> instance FV TyEntry where
>     alpha <? (a := d ::: k) = alpha <? a || alpha <? d

> instance FV NormalNum where
>     alpha <? n = isJust $ lookupVariable alpha n

> instance FV NormalPredicate where
>     alpha <? IsPos n   = alpha <? n
>     alpha <? IsZero n  = alpha <? n


> unify t u = unifyTypes t u `inLoc` (do
>                 t' <- niceType t
>                 u' <- niceType u
>                 return $ "when unifying\n        " ++ show (prettyHigh t')
>                     ++ "\n    and\n        " ++ show (prettyHigh u'))

> unifyTypes :: Type -> Type -> Contextual t ()
> -- unifyTypes s t | s == t = return ()
> unifyTypes Arr Arr = return ()
> unifyTypes (TyVar KindNum alpha) (TyVar KindNum beta) = unifyNum (NumVar alpha) (NumVar beta)
> unifyTypes (TyVar ka alpha) (TyVar kb beta) | ka /= kb   = fail "Kind mismatch in unify"
>                                             | otherwise  = onTop $
>   \ (gamma := d ::: k) -> case
>           (gamma == alpha, gamma == beta, d) of
>           (True,   True,   _)  ->  restore                                 
>           (True,   False,  Hole)      ->  replace ((alpha := Some (var k beta) ::: k) :> F0)
>           (True,   False,  Fixed)     ->  solve beta ((alpha := Fixed ::: k) :> F0) (TyVar ka alpha)
>                                       >>  replace F0
>           (False,  True,   Hole)      ->  replace ((beta := Some (var k alpha) ::: k) :> F0)
>           (False,  True,   Fixed)     ->  solve alpha ((beta := Fixed ::: k) :> F0) (TyVar kb beta)
>                                       >>  replace F0

>           (True,   False,  Some tau)  ->  unifyTypes (TyVar kb beta)   tau       >> restore   
>           (False,  True,   Some tau)  ->  unifyTypes (TyVar ka alpha)  tau       >> restore   
>           (False,  False,  _)         ->  unifyTypes (TyVar ka alpha)  (TyVar kb beta)  >> restore   

> unifyTypes (TyCon c1) (TyCon c2)
>     | c1 == c2   = return ()
>     | otherwise  = fail $ "Mismatched type constructors " ++ c1
>                               ++ " and " ++ c2

> unifyTypes (TyApp f1 s1) (TyApp f2 s2) = unifyTypes f1 f2 >> unifyTypes s1 s2


> {-
> unifyTypes (Bind b a k ty) tau = do
>     nm <- fresh a (Hole ::: k)
>     unifyTypes (unbind nm ty) tau

> unifyTypes tau (Bind b a k ty) = do
>     nm <- fresh a (Hole ::: k)
>     unifyTypes tau (unbind nm ty)

> unifyTypes (Qual p t) tau = modifyContext (:< Constraint p) >> unifyTypes t tau
> unifyTypes tau (Qual p t) = modifyContext (:< Constraint p) >> unifyTypes tau t
> -}

> unifyTypes (TyNum m)      (TyNum n)              = unifyNum m n
> unifyTypes (TyNum m)      (TyVar KindNum a)      = unifyNum m (NumVar a)
> unifyTypes (TyVar KindNum a)      (TyNum n)      = unifyNum (NumVar a) n

> unifyTypes (TyVar k alpha)  tau              =  startSolve alpha tau
> unifyTypes tau              (TyVar k alpha)  =  startSolve alpha tau
> unifyTypes tau              upsilon = errCannotUnify tau upsilon



> startSolve :: TyName -> Type -> Contextual t ()
> startSolve alpha tau = do
>     (rho, xs) <- rigidHull tau
>     solve alpha (constraintsToSuffix xs) rho
>     solveConstraints xs
>     return ()

> rigidHull :: Type -> Contextual t (Type, Fwd (TyName, TypeNum))
> rigidHull (TyVar k a)            = return (TyVar k a, F0)
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
>     (False,  True,   Some upsilon)  ->  do
>         (upsilon', xs) <- rigidHull upsilon
>         solve alpha (constraintsToSuffix xs <+> ((gamma := Some upsilon' ::: k) :> _Xi)) tau
>         solveConstraints xs
>         replace F0
>     (False,  True,   _)             ->  solve alpha ((gamma := d ::: k) :> _Xi) tau
>                                         >>  replace F0   
>     (False,  False,  _)             ->  solve alpha _Xi tau
>                                         >>  restore



> unifyNum :: TypeNum -> TypeNum -> Contextual t ()
> unifyNum (NumConst 0) n = unifyZero [] F0 =<< normaliseNum n
> unifyNum m n = unifyZero [] F0 =<< normaliseNum (m - n)


> typeToNum :: Type -> Contextual t NormalNum
> typeToNum (TyNum n)          = normaliseNum n
> typeToNum (TyVar KindNum a)  = lookupNormNumVar a
> typeToNum t = fail $ "Bad type in numeric constraint: " ++ show t

> lookupNormNumVar :: TyName -> Contextual t NormalNum
> lookupNormNumVar a = getContext >>= seek
>   where
>     seek B0 = fail $ "Missing numeric variable " ++ show a
>     seek (g :< A (b := _ ::: k))
>         | a == b && k == KindNum = return $ mkVar a
>         | a == b = fail $ "Type variable " ++ show a ++ " is not numeric"
>     seek (g :< _) = seek g


> unifyZero :: [NormalPredicate] -> Suffix -> NormalNum -> Contextual t ()
> unifyZero ps _Psi e
>   | isZero e      = return ()
>   | isConstant e  = errCannotUnify (numToType e) (TyNum (NumConst 0))
>   | otherwise     = onTopNum
>     (IsZero e, modifyContext (<>< _Psi))
>     (\ p -> unifyZero (p:ps) _Psi e) $
>     \ (alpha := d ::: KindNum) ->
>     case lookupVariable alpha e of
>         Nothing  -> unifyZero ps _Psi e >> restore
>         Just n   -> case d of
>             Some x   -> do
>                           modifyContext (<>< _Psi)
>                           x' <- typeToNum x
>                           unifyZero ps F0 (substNExp (alpha, n) x' e)
>                           restore
>             Hole   | n `dividesCoeffs` e -> do
>                           modifyContext (<>< _Psi)
>                           replace $ (alpha := Some (numToType (pivot (alpha, n) e)) ::: KindNum) :> F0
>                    | (alpha, n) `notMaxCoeff` e -> do
>                           modifyContext (<>< _Psi)
>                           (p, beta) <- insertFreshVar $ pivot (alpha, n) e
>                           unifyZero ps ((beta := Hole ::: KindNum) :> F0) $ substNExp (alpha, n) p e
>                           replace $ (alpha := Some (numToType p) ::: KindNum) :> F0
>             _ -> case findRewrite alpha ps of
>                      Just na -> do
>                          unifyZero (map (substNormPred alpha na) ps) _Psi (substNum alpha na e)
>                          restore
>                      Nothing | numVariables e > fwdLength _Psi + 1 -> do
>                           unifyZero ps ((alpha := Hole ::: KindNum) :> _Psi) e
>                           replace F0
>                              | otherwise -> fail "No way!"


> findRewrite :: TyName -> [NormalPredicate] -> Maybe NormalNum
> findRewrite a hs = join $ listToMaybe $ map (toRewrite a) hs

> toRewrite :: TyName -> NormalPredicate -> Maybe NormalNum
> toRewrite a (IsZero n) = case lookupVariable a n of
>     Just i | i `dividesCoeffs` n  -> Just $ pivot (a, i) n
>     _                             -> Nothing
> toRewrite a (IsPos _) = Nothing



We can insert a fresh variable into a unit thus:

> insertFreshVar :: NormalNum -> Contextual t (NormalNum, TyName)
> insertFreshVar d = do
>     n <- freshName
>     let beta = ("beta", n)
>     return (d +~ mkVar beta, beta)