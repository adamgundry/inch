> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances, GADTs,
>              RankNTypes #-}

> module Unify where

> import Control.Applicative
> import Control.Monad hiding (mapM_)
> import Data.Foldable 
> import Data.Maybe
> import Data.Monoid hiding (All)
> import Control.Monad.State (gets)
> import Prelude hiding (any, mapM_)
> import Text.PrettyPrint.HughesPJ

> import BwdFwd
> import TyNum
> import Kind
> import Type
> import Syntax
> import Context
> import Num
> import Kit
> import Error
> import PrettyPrinter
> import PrettyContext

> data Extension = Restore | Replace Suffix

> onTop ::  (forall k. TyEntry k -> Contextual t Extension)
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
>         B0 -> erk $ "onTop: ran out of context"

> onTopNum ::  (NormalPredicate, Contextual t ()) ->
>                  (TyEntry KNum -> Contextual t Extension) ->
>                  Contextual t ()
> onTopNum (p, m) f = do
>   g <- getContext
>   case g of
>     _Gamma :< xD -> do  
>       putContext _Gamma
>       case xD of
>         A (a@(FVar _ KNum) := d) -> ext xD =<< f (a := d)
>         Layer pt@(PatternTop _ _ _ cs) -> do
>             m
>             modifyContext (:< Layer (pt{ptConstraints = p : cs}))
>         Layer GenMark -> do
>             m
>             modifyContext (:< Layer GenMark)
>             modifyContext (:< Constraint Wanted p)
> {-
>         Constraint Given _ -> do
>             m
>             modifyContext $ (:< xD) . (:< Constraint Wanted p)
> -}
>         _ -> onTopNum (p, m) f >> modifyContext (:< xD)
>     B0 -> inLocation (text "when solving" <+> prettyHigh (fogSysPred $ reifyPred p)) $
>               erk $ "onTopNum: ran out of context"

> restore :: Contextual t Extension
> restore = return Restore

> replace :: Suffix -> Contextual t Extension
> replace = return . Replace

> ext :: Entry -> Extension -> Contextual t ()
> ext xD (Replace _Xi)  = modifyContext (<>< _Xi)
> ext xD Restore        = modifyContext (:< xD)


> var k a = TyVar (FVar a k)


> unify :: Type k -> Type k -> Contextual () ()
> unify t u = unifyTypes t u `inLoc` (do
>                 return $ sep [text "when unifying", nest 4 (prettyHigh $ fogSysTy t),
>                              text "and", nest 4 (prettyHigh $ fogSysTy u)])
>                     -- ++ "\n    in context " ++ render g)

> unifyTypes :: Type k -> Type k -> Contextual t ()
> -- unifyTypes s t | s == t = return ()
> unifyTypes Arr Arr  = return ()
> unifyTypes (TyVar a@(FVar _ KNum)) (TyVar b) =
>     unifyNum (NumVar a) (NumVar b)
> unifyTypes (TyVar alpha) (TyVar beta) = onTop $
>   \ (gamma := d) ->
>     hetEq gamma alpha
>       (hetEq gamma beta
>         restore
>         (case d of
>           Hole      ->  replace (TE (alpha := Some (TyVar beta)) :> F0)
>           Some tau  ->  unifyTypes (TyVar beta) tau
>                             >> restore
>           _         ->  solve beta (TE (alpha := d) :> F0) (TyVar alpha)
>                             >> replace F0
>         )
>       )
>       (hetEq gamma beta
>         (case d of
>           Hole      ->  replace (TE (beta := Some (TyVar alpha)) :> F0)
>           Some tau  ->  unifyTypes (TyVar alpha) tau
>                             >> restore
>           _         ->  solve alpha (TE (beta := d) :> F0) (TyVar beta)
>                             >> replace F0
>         )
>         (unifyTypes (TyVar alpha)  (TyVar beta)  >> restore)
>       )

> unifyTypes (TyCon c1 _) (TyCon c2 _)
>     | c1 == c2   = return ()
>     | otherwise  = erk $ "Mismatched type constructors " ++ c1
>                               ++ " and " ++ c2

> unifyTypes (TyApp f1 s1) (TyApp f2 s2) =
>     hetEq (getTyKind f1) (getTyKind f2)
>         (unifyTypes f1 f2 >> unifyTypes s1 s2)
>         (erk "Mismatched kinds")



> {-
> unifyTypes (Bind b1 a1 k1 t1) (Bind b2 a2 k2 t2) | b1 == b2 && k1 == k2 = do
>     nm <- fresh (a1 ++ "_u") (Fixed ::: KNum)
>     unifyTypes (unbind nm t1) (unbind nm t2)
> -}

> {-
> unifyTypes (Bind b a k ty) tau = do
>     nm <- fresh a (Hole ::: k)
>     unifyTypes (unbind nm ty) tau

> unifyTypes tau (Bind b a k ty) = do
>     nm <- fresh a (Hole ::: k)
>     unifyTypes tau (unbind nm ty)
> -}


> -- unifyTypes (Qual p s) (Qual q t) | p == q = unifyTypes s t

> {-
> unifyTypes (Qual p t) tau = do
>     p <- normalisePred p
>     modifyContext (:< Constraint Wanted p)
>     unifyTypes t tau
> unifyTypes tau (Qual p t) = do
>     p <- normalisePred p
>     modifyContext (:< Constraint Wanted p)
>     unifyTypes tau t
> -}

> {-
> unifyTypes (Qual p s) (Qual q t) = do
>     unifyTypes s t
>     g <- getContext
>     let p' = expandPred g p
>         q' = expandPred g q
>     unless (p' == q') $ erk $ "Mismatched qualifiers " ++ renderMe p' ++ " and " ++ renderMe q'
> -}

> unifyTypes (TyNum m)      (TyNum n)      = unifyNum m n
> unifyTypes (TyNum m)      (TyVar a)      = unifyNum m (NumVar a)
> unifyTypes (TyVar a)      (TyNum n)      = unifyNum (NumVar a) n
> unifyTypes (TyVar alpha)  tau            = startSolve alpha tau
> unifyTypes tau            (TyVar alpha)  = startSolve alpha tau
> unifyTypes tau            upsilon        = errCannotUnify (fogTy tau) (fogTy upsilon)



> startSolve :: Var () k -> Type k -> Contextual t ()
> startSolve alpha tau = do
>     (rho, xs) <- rigidHull tau
>     solve alpha (pairsToSuffix xs) rho
>     unifyPairs xs

> makeFlex :: TypeNum -> Contextual t (Type KNum, Fwd (Var () KNum, TypeNum))
> makeFlex n = do  v <- freshVar SysVar "_i" KNum
>                  return (TyNum (NumVar v), (v, n) :> F0)

> rigidHull :: Type k -> Contextual t (Type k, Fwd (Var () KNum, TypeNum))
> rigidHull (TyVar a)    = case varKind a of
>                              KNum  -> makeFlex (NumVar a)
>                              _     -> return (TyVar a, F0)
> rigidHull (TyCon c k)  = return (TyCon c k, F0)
> rigidHull (TyApp f s)  = do  (f',  xs  )  <- rigidHull f
>                              (s',  ys  )  <- rigidHull s
>                              return (TyApp f' s', xs <.> ys)
> rigidHull Arr          = return (Arr, F0)
> rigidHull (TyNum n)    = makeFlex n

> rigidHull (Bind All x k b) | not (k =?= KNum) = do
>     v <- freshVar SysVar "_magic" k
>     (t, cs) <- rigidHull (unbindTy v b)
>     return (Bind All x k (bindTy v t), cs)

> {-
> rigidHull (Bind Pi x KNum b) = do
>     n <- freshName
>     (t, cs) <- rigidHull (unbind ("magic", n) b)
>     return (Bind Pi x KNum (bind ("magic", n) t), dropMagic ("magic", n) cs)
>   where
>     dropMagic :: Eq a => a -> Fwd (a, b) -> Fwd (a, b)
>     dropMagic a F0 = F0
>     dropMagic a ((x, y) :> xys) | x == a     = dropMagic a xys
>                                 | otherwise  = (x, y) :> dropMagic a xys
> -}

> rigidHull (Qual p t) = (\ (t, cs) -> (Qual p t, cs)) <$> rigidHull t


> rigidHull b = erk $ "rigidHull can't cope with " ++ renderMe (fogSysTy b)


> pairsToSuffix :: Fwd (Var () KNum, TypeNum) -> Suffix
> pairsToSuffix = fmap (TE . (:= Hole) . fst)

> unifyPairs :: Fwd (Var () KNum, TypeNum) -> Contextual t ()
> unifyPairs = mapM_ (uncurry $ unifyNum . NumVar)


> solve :: Var () k -> Suffix -> Type k -> Contextual t ()
> solve alpha _Xi tau = onTop $
>   \ (gamma := d) -> let occurs = gamma <? tau || gamma <? _Xi in
>     hetEq gamma alpha
>       (if occurs
>          then erk "Occurrence detected!"
>          else case d of
>            Hole          ->  replace (_Xi <.> (TE (alpha := Some tau) :> F0))
>            Some upsilon  ->  modifyContext (<>< _Xi)
>                                         >>  unifyTypes upsilon tau
>                                         >>  restore
>            _             ->  errUnifyFixed alpha tau
>       )
>       (if occurs
>         then case d of
>           Some upsilon  ->  do
>             (upsilon', xs) <- rigidHull upsilon
>             solve alpha (pairsToSuffix xs <.> (TE (gamma := Some upsilon') :> _Xi)) tau
>             unifyPairs xs
>             replace F0
>           _             ->  solve alpha (TE (gamma := d) :> _Xi) tau
>                                         >>  replace F0   
>         else solve alpha _Xi tau >>  restore
>       )



> unifyNum :: TypeNum -> TypeNum -> Contextual t ()
> unifyNum (NumConst 0)  n = unifyZero F0 =<< normaliseNum n
> unifyNum m             n = unifyZero F0 =<< normaliseNum (m - n)

> constrainZero :: NormalNum -> Contextual t ()
> constrainZero e = modifyContext (:< Constraint Wanted (IsZero e))

> unifyZero :: Suffix -> NormalNum -> Contextual t ()
> unifyZero _Psi e
>   | isZero e      = return ()
>   | isConstant e  = errCannotUnify (fogTy (numToType e)) (STyNum (NumConst 0))
>   | otherwise     = onTopNum (IsZero e, modifyContext (<>< _Psi)) $
>     \ (alpha := d) ->
>     case lookupVariable alpha e of
>       Nothing -> unifyZero _Psi e >> restore
>       Just n -> case d of
>         Some x -> do
>             modifyContext (<>< _Psi)
>             x' <- normaliseNum (toNum x)
>             unifyZero F0 (substNum alpha x' e)
>             restore
>         Hole  | n `dividesCoeffs` e -> do
>                   modifyContext (<>< _Psi)
>                   replace $ TE (alpha := Some (numToType (pivot (alpha, n) e))) :> F0
>               | (alpha, n) `notMaxCoeff` e -> do
>                   modifyContext (<>< _Psi)
>                   error "this really ought to be tested"
>                   (p, beta) <- insertFreshVar $ pivot (alpha, n) e
>                   unifyZero (TE (beta := Hole) :> F0) $ substNExp (alpha, n) p e
>                   replace $ TE (alpha := Some (numToType p)) :> F0
>         _  | numVariables e > fwdLength _Psi + 1 -> do
>                          unifyZero (TE (alpha := d) :> _Psi) e
>                          replace F0
>            | otherwise -> do
>                modifyContext (:< A (alpha := d))
>                modifyContext (<>< _Psi)
>                constrainZero e
>                replace F0


> subsPreds a dn = map (substNormPred a dn)

> findRewrite :: Var () KNum -> [NormalPredicate] -> Maybe NormalNum
> findRewrite a hs = listToMaybe $ catMaybes $ map (toRewrite a) hs

> toRewrite :: Var () KNum -> NormalPredicate -> Maybe NormalNum
> toRewrite a (IsZero n) = case lookupVariable a n of
>     Just i | i `dividesCoeffs` n  -> Just $ pivot (a, i) n
>     _                             -> Nothing
> toRewrite a (IsPos _) = Nothing



We can insert a fresh variable into a unit thus:

> insertFreshVar :: NormalNum -> Contextual t (NormalNum, Var () KNum)
> insertFreshVar d = do
>     v <- freshVar SysVar "_beta" KNum
>     return (d +~ mkVar v, v)



> unifyFun :: Rho -> Contextual () (Sigma, Rho)
> unifyFun (TyApp (TyApp Arr s) t) = return (s, t)
> unifyFun ty = do
>     s <- unknownTyVar "_s" KSet
>     t <- unknownTyVar "_t" KSet
>     unify (s --> t) ty
>     return (s, t)





> traceContext s = getContext >>= \ g -> mtrace (s ++ "\n" ++ renderMe g)