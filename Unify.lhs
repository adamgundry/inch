> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances, GADTs,
>              RankNTypes #-}

> module Unify where

> import Control.Applicative
> import Control.Monad hiding (mapM_)
> import Data.Foldable hiding (elem)
> import Data.List
> import Data.Maybe
> import Prelude hiding (any, mapM_)
> import Text.PrettyPrint.HughesPJ

> import BwdFwd
> import Kind
> import Type
> import TyNum
> import Context
> import Kit
> import Error
> import PrettyPrinter
> import PrettyContext ()
> import Check

> data Extension = Restore | Replace Suffix

> onTop ::  (forall k. TyEntry k -> Contextual Extension)
>             -> Contextual ()
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

> onTopNum ::  (Predicate, Contextual ()) ->
>                  (TyEntry KNum -> Contextual Extension) ->
>                  Contextual ()
> onTopNum (p, m) f = do
>   g <- getContext
>   case g of
>     _Gamma :< xD -> do  
>       putContext _Gamma
>       case xD of
>         A (a@(FVar _ KNum) := d) -> ext xD =<< f (a := d)
>         Layer l | layerStops l -> do
>             m
>             modifyContext (:< Layer l)
>             modifyContext (:< Constraint Wanted p)
>         _ -> onTopNum (p, m) f >> modifyContext (:< xD)
>     B0 -> inLocation (text "when solving" <+> prettyHigh (fogSysPred p)) $
>               erk $ "onTopNum: ran out of context"

> restore :: Contextual Extension
> restore = return Restore

> replace :: Suffix -> Contextual Extension
> replace = return . Replace

> ext :: Entry -> Extension -> Contextual ()
> ext xD (Replace _Xi)  = modifyContext (<>< _Xi)
> ext xD Restore        = modifyContext (:< xD)


> var k a = TyVar (FVar a k)


> unifyList :: KindI k => [Type k] -> Contextual (Type k)
> unifyList []      = unknownTyVar "_ul" kind
> unifyList (t:ts)  = mapM_ (unify t) ts >> return t


> unify :: Type k -> Type k -> Contextual ()
> unify t u = verifyContext True "unify" >> unifyTypes t u `inLoc` (do
>                 return $ sep [text "when unifying", nest 4 (prettyHigh $ fogSysTy t),
>                              text "and", nest 4 (prettyHigh $ fogSysTy u)])
>                     -- ++ "\n    in context " ++ render g)

> unifyTypes :: Type k -> Type k -> Contextual ()
> -- unifyTypes s t | s == t = return ()
> unifyTypes Arr Arr  = return ()
> unifyTypes s t | KNum <- getTyKind s = unifyNum s t
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

> unifyTypes (UnOp o)       (UnOp o')  | o == o' = return ()
> unifyTypes (BinOp o)      (BinOp o') | o == o' = return ()

> unifyTypes (TyVar alpha)  tau            = startSolve alpha tau
> unifyTypes tau            (TyVar alpha)  = startSolve alpha tau
> unifyTypes tau            upsilon        = errCannotUnify (fogTy tau) (fogTy upsilon)



> startSolve :: Var () k -> Type k -> Contextual ()
> startSolve alpha tau = do
>     (rho, xs) <- rigidHull [] tau
>     -- traceContext $ "sS\nalpha = " ++ show alpha ++ "\ntau = " ++ show tau ++ "\nrho = " ++ show rho ++ "\nxs = " ++ show xs
>     solve alpha (pairsToSuffix xs) rho
>     -- traceContext $ "sS2"
>     unifyPairs xs

> type FlexConstraint = (Var () KNum, TypeNum, TypeNum)

> makeFlex :: [Var () KNum] -> Type KNum ->
>                 Contextual (Type KNum, Fwd FlexConstraint)
> makeFlex as n = do
>     let n' = normaliseNum n
>     let (l, r) = partitionNum as n'
>     if isZero r
>         then return (n, F0)
>         else do
>             v <- freshVar SysVar "_i" KNum
>             -- traceContext $ "mF\nas = " ++ show as ++ "\nn = " ++ show n ++ "\nl' = " ++ show l' ++ "\nr' = " ++ show r'
>             return (reifyNum (mkVar v + l), (v, TyVar v, reifyNum r) :> F0)



> rigidHull :: [Var () KNum] -> Type k ->
>                  Contextual (Type k, Fwd FlexConstraint)

> rigidHull as t | KNum <- getTyKind t = makeFlex as t

> rigidHull as (TyVar a)    = return (TyVar a, F0)
> rigidHull as (TyCon c k)  = return (TyCon c k, F0)
> rigidHull as Arr          = return (Arr, F0)
> rigidHull as (BinOp o)    = return (BinOp o, F0)

> rigidHull as (TyApp f s)  = do  (f',  xs  )  <- rigidHull as f
>                                 (s',  ys  )  <- rigidHull as s
>                                 return (TyApp f' s', xs <.> ys)

> rigidHull as (Bind b x KNum t) = do
>     v <- freshVar SysVar "_magical" KNum
>     (t, cs) <- rigidHull (v:as) (unbindTy v t)
>     return (Bind b x KNum (bindTy v t), cs)

> rigidHull as (Bind All x k b) | not (k =?= KNum) = do
>     v <- freshVar SysVar "_magic" k
>     (t, cs) <- rigidHull as (unbindTy v b)
>     return (Bind All x k (bindTy v t), cs)

This is wrong, I think:

> rigidHull as (Qual p t) = (\ (t, cs) -> (Qual p t, cs)) <$> rigidHull as t

> rigidHull as b = erk $ "rigidHull can't cope with " ++ renderMe (fogSysTy b)



> pairsToSuffix :: Fwd FlexConstraint -> Suffix
> pairsToSuffix = fmap (TE . (:= Hole) . fst3)
>   where fst3 (a, _, _) = a

> unifyPairs :: Fwd FlexConstraint -> Contextual ()
> unifyPairs = mapM_ (uncurry unifyNum . snd3)
>   where snd3 (_, b, c) = (b, c)


> solve :: Var () k -> Suffix -> Type k -> Contextual ()
> solve alpha _Xi tau = onTop $
>   \ (gamma := d) -> let occurs = gamma <? tau || gamma <? _Xi in
>     hetEq gamma alpha
>       (if occurs
>          then erk $ "Occurrence of " ++ fogSysVar alpha
>                     ++ " detected when unifying with "
>                     ++ renderMe (fogTy tau)
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
>             (upsilon', xs) <- rigidHull [] upsilon
>             solve alpha (pairsToSuffix xs <.> (TE (gamma := Some upsilon') :> _Xi)) tau
>             unifyPairs xs
>             replace F0
>           _             ->  solve alpha (TE (gamma := d) :> _Xi) tau
>                                         >>  replace F0   
>         else solve alpha _Xi tau >>  restore
>       )



> unifyNum :: TypeNum -> TypeNum -> Contextual ()
> unifyNum (TyInt 0)  n = unifyZero F0 (normaliseNum n)
> unifyNum m          n = unifyZero F0 (normaliseNum (m - n))

> constrainZero :: NormalNum -> Contextual ()
> constrainZero e = modifyContext (:< Constraint Wanted (reifyNum e %==% 0))

> unifyZero :: Suffix -> NormalNum -> Contextual ()
> unifyZero _Psi e = case getConstant e of
>   Just k  | k == 0     -> return ()
>           | otherwise  -> errCannotUnify (fogTy (reifyNum e)) (STyInt 0)
>   Nothing              -> onTopNum (reifyNum e %==% 0, modifyContext (<>< _Psi)) $
>     \ (a := d) ->
>       case (d, solveFor a e) of
>         (Some t,  _)           -> do  modifyContext (<>< _Psi)
>                                       unifyZero F0 (substNum a t e)
>                                       restore
>         (_,       Absent)      -> do  unifyZero _Psi e
>                                       restore
>         (Hole,    Solve n)     -> do  modifyContext (<>< _Psi)
>                                       replace $ TE (a := Some (reifyNum n)) :> F0
>         (Hole,    Simplify n)  -> do  modifyContext (<>< _Psi)
>                                       (p, b) <- insertFreshVar n
>                                       let p' = reifyNum p
>                                       unifyZero (TE (b := Hole) :> F0) $ substNum a p' e
>                                       replace $ TE (a := Some p') :> F0
>         _  | varsLeft -> do
>                          unifyZero (TE (a := d) :> _Psi) e
>                          replace F0
>            | otherwise -> do
>                modifyContext (:< A (a := d))
>                modifyContext (<>< _Psi)
>                constrainZero e
>                replace F0
>           where varsLeft = not . null $ vars e \\ vars _Psi

We can insert a fresh variable into a unit thus:

> insertFreshVar :: NormalNum -> Contextual (NormalNum, Var () KNum)
> insertFreshVar d = do
>     v <- freshVar SysVar "_beta" KNum
>     return (d + mkVar v, v)



> unifyFun :: Rho -> Contextual (Sigma, Rho)
> unifyFun (TyApp (TyApp Arr s) t) = return (s, t)
> unifyFun ty = do
>     s <- unknownTyVar "_s" KSet
>     t <- unknownTyVar "_t" KSet
>     unify (s --> t) ty
>     return (s, t)
