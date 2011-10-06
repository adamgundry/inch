> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts, PatternGuards,
>              RankNTypes #-}

> module Solver where

> import Control.Applicative hiding (Alternative)
> import Control.Monad
> import Control.Monad.Writer hiding (All)
> import Data.Maybe
> import Data.Traversable

> import qualified Data.Integer.Presburger as P
> import Data.Integer.Presburger (Formula (TRUE, FALSE, (:=:), (:<:), (:<=:), (:>:), (:>=:), (:\/:), (:/\:), (:=>:)))

> import BwdFwd
> import Kind 
> import Type
> import TyNum
> import Context
> import Unify
> import Kit
> import Error


> unifySolveConstraints :: Contextual t ()
> unifySolveConstraints = do
>     (g, ns) <- runWriter . collectEqualities <$> getContext
>     putContext g
>     traverse (uncurry unifyNum) ns
>     return ()
>   where
>     collectEqualities :: Context -> Writer [(Type KNum, Type KNum)] Context
>     collectEqualities B0 = return B0
>     collectEqualities (g :< Layer l) | layerStops l  = return $ g :< Layer l
>                                      | otherwise     = (:< Layer l) <$> collectEqualities g
>     collectEqualities (g :< Constraint Wanted (P EL m n)) = tell [(m, n)]
>         >> collectEqualities g
>     collectEqualities (g :< e) = (:< e) <$> collectEqualities g


> trySolveConstraints :: Contextual t ([Predicate], [Predicate])
> trySolveConstraints = do
>     g <- getContext
>     let (g', hs, ps) = collect g [] []
>     putContext g'
>     qs <- filterM (formulaic hs) ps
>     return (hs, qs)
>   where
>     formulaic hs p = (not . P.check) <$> toFormula hs p
>
>     collect :: Context -> [Predicate] -> [Predicate] ->
>                    (Context, [Predicate], [Predicate])
>     collect B0 hs ps = (B0, hs, ps)
>     collect (g :< Constraint Wanted p)  hs ps = collect g hs (p:ps)
>     collect (g :< Constraint Given h)   hs ps =
>         collect g (h:hs) ps <:< Constraint Given h
>     collect (g :< A e@(a@(FVar _ KNum) := Some d)) hs ps =
>         collect g (subsPreds a d hs) (subsPreds a d ps) <:< A e
>     collect (g :< Layer l) hs ps | layerStops l  = (g :< Layer l, collectHyps g hs, ps)
>                                  | otherwise     = collect g hs ps <:< Layer l
>     collect (g :< e) hs ps = collect g hs ps <:< e
>
>     collectHyps B0 hs = hs
>     collectHyps (g :< Constraint Given h) hs = collectHyps g (h:hs)
>     collectHyps (g :< _) hs = collectHyps g hs

>     (g, a, b) <:< e = (g :< e, a, b)

>     subsPreds :: Var () KNum -> Type KNum -> [Predicate] -> [Predicate]
>     subsPreds a n = map (fmap (replaceTy a n))

> solveConstraints :: Contextual t ()
> solveConstraints = do
>     (hs, qs) <- trySolveConstraints
>     case qs of
>         []  -> return ()
>         _   -> errCannotDeduce hs qs

> solveOrSuspend :: Contextual t ()
> solveOrSuspend = want . snd =<< trySolveConstraints
>   where
>     want :: [Predicate] -> Contextual t ()
>     want [] = return ()
>     want (p:ps)
>         | nonsense p  = errImpossiblePred p
>         | otherwise   = modifyContext (:< Constraint Wanted p)
>                                 >> want ps
>
>     nonsense :: Predicate -> Bool
>     nonsense (P c m n) = maybe False (nonc c) (getConstant (normaliseNum (m - n)))
>     
>     nonc EL = (/= 0)
>     nonc LE = (> 0)
>     nonc LS = (>= 0)
>     nonc GE = (< 0)
>     nonc GR = (<= 0)


> toFormula :: [Predicate] -> Predicate ->
>                  Contextual t P.Formula
> toFormula hs p = do
>     g <- getContext
>     let hs'  = map (normalisePred . expandPred g) hs
>         p'   = normalisePred $ expandPred g p
>     case trivialPred p' of
>         Just True   -> return TRUE
>         Just False  -> return FALSE
>         Nothing     -> do
>             let f = convert (expandContext g) [] hs' p'
>             -- mtrace $ "toFormula [" ++ intercalate "," (map (renderMe . fogPred) hs) ++ "] => (" ++ renderMe (fogPred p) ++ ")"
>             -- mtrace (show f)
>             return f
>   where
>     convert :: Context -> [(Var () KNum, P.Term)] -> [NormalPredicate] ->
>                    NormalPredicate -> P.Formula
>     convert B0 axs hs p =
>         let hs'  = map (predToFormula True axs) hs
>             p'   = predToFormula False axs p
>         in foldr (:/\:) TRUE hs' :=>: p'
>     convert (g :< A (a@(FVar _ KNum) := d)) axs hs p | any (a <?) (p:hs) = 
>         P.Forall (\ x -> convert g ((a, x) : axs) hs p)
>     convert (g :< _) axs hs p = convert g axs hs p
                
>     predToFormula :: Bool -> [(Var () KNum, P.Term)] -> NormalPredicate -> P.Formula
>     predToFormula hyp axs (P c m n) = linearise axs m $ \ m' ->
>                                       linearise axs n $ \ n' ->
>                                           compToFormula c m' n'

> {-
>     predToFormula hyp xs (Op Max m n t) =
>         let m'  = numToTerm xs m
>             n'  = numToTerm xs n
>             t'  = numToTerm xs t
>         in ((m' :=: t') :/\: (m' :>=: n'))
>                    :\/: ((n' :=: t') :/\: (n' :>=: m'))
>     predToFormula hyp _ (Op _ _ _ _) = if hyp then TRUE else FALSE
> -}

>     linearise ::  [(Var () KNum, P.Term)] -> NormalNum ->
>                     (P.Term -> P.Formula) -> P.Formula
>     linearise axs (NN i bs ts) f = help x ts
>       where
>         x = fromInteger i + foldr (\ (b, k) t -> fromJust (lookup b axs) * fromInteger k + t) 0 bs
>
>         help :: P.Term -> [(Type KNum, Integer)] -> P.Formula
>         help t []      = f t
>         help t ((TyApp (UnOp o) m, k):ks) | Just lo <- linUnOp o =
>             linearise axs (normaliseNum m) $ \ m' ->
>                 P.Exists $ \ y ->
>                     lo m' y :/\: help (t + fromInteger k * y) ks
>         help t ((TyApp (TyApp (BinOp o) m) n, k):ks) | Just lo <- linBinOp o =
>             linearise axs (normaliseNum m) $ \ m' ->
>             linearise axs (normaliseNum n) $ \ n' ->
>                 P.Exists $ \ y ->
>                     lo m' n' y :/\: help (t + fromInteger k * y) ks
>         help t ((_, k):ks)  = P.Forall (\ y -> help (t + fromInteger k * y) ks)

>     linUnOp :: UnOp -> Maybe (P.Term -> P.Term -> P.Formula)
>     linUnOp Abs = Just $ \ m y -> ((m :=: y) :/\: (m :>=: 0))
>                                       :\/: ((m :=: -y) :/\: (m :<: 0))
>     linUnOp Signum = Just $ \ m y -> ((y :=: 1) :/\: (m :>: 0))
>                                       :\/: ((y :=: -1) :/\: (m :<: 0))
>                                       :\/: ((y :=: 0) :/\: (m :=: 0))

>     linBinOp :: BinOp -> Maybe (P.Term -> P.Term -> P.Term -> P.Formula)
>     linBinOp Max = Just $ \ m n y -> ((m :=: y) :/\: (m :>=: n))
>                                       :\/: ((n :=: y) :/\: (n :>=: m))
>     linBinOp Min = Just $ \ m n y -> ((m :=: y) :/\: (m :<=: n))
>                                       :\/: ((n :=: y) :/\: (n :<=: m))
>     linBinOp _ = Nothing

>     compToFormula :: Comparator -> P.Term -> P.Term -> P.Formula
>     compToFormula EL  = (:=:)
>     compToFormula LE  = (:<=:)
>     compToFormula LS  = (:<:)
>     compToFormula GE  = (:>=:)
>     compToFormula GR  = (:>:)


