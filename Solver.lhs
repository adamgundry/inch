> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts, PatternGuards,
>              RankNTypes #-}

> module Solver where

> import Control.Applicative hiding (Alternative)
> import Control.Monad
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Maybe
> import Data.Traversable

> import qualified Data.Integer.Presburger as P
> import Data.Integer.Presburger (Formula (TRUE, FALSE, (:=:), (:<:), (:<=:), (:>:), (:>=:), (:\/:), (:/\:), (:=>:)), (.*))

> import BwdFwd
> import Kind 
> import Type
> import TyNum
> import Context
> import Unify
> import Kit
> import Error

> import Debug.Trace
> import PrettyPrinter


> unifySolveConstraints :: Contextual ()
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


> trySolveConstraints :: Contextual ([Predicate], [Predicate])
> trySolveConstraints = do
>     g <- getContext
>     let (g', vs, hs, ps) = collect g [] [] []
>     putContext g'
>     let qs = simplifyConstraints vs hs ps
>     return (hs, qs)
>   where
>     collect :: Context -> [Var () KNum] -> [Predicate] -> [Predicate] ->
>                    (Context, [Var () KNum], [Predicate], [Predicate])
>     collect B0 vs hs ps = (B0, vs, hs, ps)
>     collect (g :< Constraint Wanted p)  vs hs ps = collect g vs hs (p:ps)
>     collect (g :< Constraint Given h)   vs hs ps =
>         collect g vs (h:hs) ps <:< Constraint Given h
>     collect (g :< A e@(a@(FVar _ KNum) := Some d)) vs hs ps =
>         collect g vs (subsPreds a d hs) (subsPreds a d ps) <:< A e
>     collect (g :< A e@(a@(FVar _ KNum) := _)) vs hs ps | a <? (hs, ps) =
>         collect g (a:vs) hs ps <:< A e
>     collect (g :< Layer l) vs hs ps  | layerStops l  = (g :< Layer l, vs', hs', ps')
>                                      | otherwise     = collect g vs hs ps <:< Layer l
>         where (vs', hs', ps') = collectHyps g vs hs ps
>     collect (g :< e) vs hs ps = collect g vs hs ps <:< e
>
>     collectHyps ::  Context -> [Var () KNum] -> [Predicate] -> [Predicate] ->
>                         ([Var () KNum], [Predicate], [Predicate])
>     collectHyps B0 vs hs ps = (vs, hs, ps)
>     collectHyps (g :< Constraint Given h) vs hs ps = collectHyps g vs (h:hs) ps
>     collectHyps (g :< A e@(a@(FVar _ KNum) := Some d)) vs hs ps =
>         collectHyps g vs (subsPreds a d hs) (subsPreds a d ps)
>     collectHyps (g :< A e@(a@(FVar _ KNum) := _)) vs hs ps | a <? (hs, ps) =
>         collectHyps g (a:vs) hs ps
>     collectHyps (g :< _) vs hs ps = collectHyps g vs hs ps

>     (g, a, b, c) <:< e = (g :< e, a, b, c)

>     subsPreds :: Var () KNum -> Type KNum -> [Predicate] -> [Predicate]
>     subsPreds a n = map (fmap (replaceTy a n))

> solveConstraints :: Contextual ()
> solveConstraints = do
>     (hs, qs) <- trySolveConstraints
>     case qs of
>         []  -> return ()
>         _   -> errCannotDeduce hs qs

> solveOrSuspend :: Contextual ()
> solveOrSuspend = want . snd =<< trySolveConstraints
>   where
>     want :: [Predicate] -> Contextual ()
>     want [] = return ()
>     want (p:ps)
>         | nonsense p  = errImpossiblePred p
>         | otherwise   = modifyContext (:< Constraint Wanted p)
>                                 >> want ps
>
>     nonsense :: Predicate -> Bool
>     nonsense = maybe False not . trivialPred . normalisePred


> simplifyConstraints :: [Var () KNum] -> [Predicate] -> [Predicate] -> [Predicate]
> simplifyConstraints vs hs ps = filter (not . checkPred) (nub ps)
>   where
>     -- Compute the transitive dependency closure of the variables that occur in p.
>     -- We have to keep iterating until we reach a fixed point. This
>     -- will produce the minimum set of variables and hypotheses on
>     -- which the solution of p can depend.
>     iterDeps :: ([Var () KNum], [Predicate]) -> ([Var () KNum], [Predicate]) ->
>                   ([Var () KNum], [Predicate]) -> ([Var () KNum], [Predicate])
>     iterDeps old             ([], [])         _                = old
>     iterDeps (oldVs, oldHs)  (newVs, newHs)  (poolVs, poolHs)  =
>         iterDeps (oldVs ++ newVs, oldHs ++ newHs) (newVs', newHs') (poolVs', poolHs')
>       where
>         (newVs', poolVs') = partition (<? newHs) poolVs
>         (newHs', poolHs') = partition (newVs <<?) poolHs
>
>     checkPred :: Predicate -> Bool
>     checkPred p = P.check . toFormula xs' (map normalisePred phs') . normalisePred $ p'
>       where
>         (pvs, pool)  = partition (<? p) vs
>         (xs, phs)    = iterDeps ([], []) (pvs, []) (pool, hs)
>         (xs', phs', p')   = elimEquations xs phs p 

>     elimEquations :: [Var () KNum] -> [Predicate] -> Predicate ->
>                          ([Var () KNum], [Predicate], Predicate)
>     elimEquations xs hs p = help xs [] hs p
>       where
>         help :: [Var () KNum] -> [Predicate] -> [Predicate] -> Predicate ->
>                     ([Var () KNum], [Predicate], Predicate)
>         help xs ohs []      p = (xs, ohs, p)
>         help xs ohs (h@(P EL m n):hs) p = case solveForAny (normaliseNum (n - m)) of
>             Just (a, t)  -> help xs [] (map (fmap (replaceTy a t')) (hs ++ ohs))
>                                 (fmap (replaceTy a t') p)
>               where t' = reifyNum t
>             Nothing      -> help xs (h:ohs) hs p
>         help xs ohs (h:hs) p = help xs (h:ohs) hs p


> toFormula :: [Var () KNum] -> [NormalPredicate] -> NormalPredicate -> P.Formula
> toFormula vs hs p = 

<  trace (unlines ["toFormula", "[" ++ intercalate "," (map fogSysVar vs) ++ "]","[" ++ intercalate "," (map (renderMe . fogSysPred . reifyPred) hs) ++ "]","(" ++ renderMe (fogSysPred $ reifyPred p) ++ ")"]) $

>   case trivialPred p of
>     Just True   -> TRUE
>     Just False  -> FALSE
>     Nothing -- | null hs && isSimple p  -> FALSE
>             | p `elem` hs            -> TRUE
>     Nothing     -> let r = convert vs []
>                    in {- trace ("result: " ++ show r) -} r
>                   
>   where
>     convert :: [Var () KNum] -> [(Var () KNum, P.Term)] -> P.Formula
>     convert []      axs = gogo axs hs Map.empty $ \ hs' mts' ->
>                              predToFormula False axs p mts' $ \ p' mts'' ->
>                                  hs' :=>: p'
>     convert (v:vs)  axs = P.Forall (\ t -> convert vs ((v, t) : axs))
                
>     gogo :: [(Var () KNum, P.Term)] -> [NormalPredicate] -> Map Monomial P.Term ->
>                 (P.Formula -> Map Monomial P.Term -> P.Formula) -> P.Formula
>     gogo axs []      mts f = f TRUE mts
>     gogo axs (h:hs)  mts f = predToFormula True axs h mts $ \ h' mts' ->
>                                  gogo axs hs mts' (\ x -> f (h' :/\: x))

>     predToFormula :: Bool -> [(Var () KNum, P.Term)] -> NormalPredicate ->
>                          Map Monomial P.Term ->
>                          (P.Formula -> Map Monomial P.Term -> P.Formula) -> P.Formula
>     predToFormula hyp axs (P c m n) mts f  = linearise axs m mts $ \ m' mts' ->
>                                                linearise axs n mts' $ \ n' mts'' ->
>                                                  f (compToFormula c m' n') mts''
>     predToFormula hyp axs (p :=> q) mts f  = predToFormula hyp axs q mts f

>     linearise ::  [(Var () KNum, P.Term)] -> NormalNum ->
>                     Map Monomial P.Term ->
>                     (P.Term -> Map Monomial P.Term -> P.Formula) -> P.Formula
>     linearise axs n mts f = help 0 (Map.toList (elimNN n)) mts
>       where
>         help :: P.Term -> [(Monomial, Integer)] ->
>                     Map Monomial P.Term -> P.Formula
>         help t []            mts = f t mts
>         help t ((ys, k):ks)  mts = case getLinearMono ys of
>             Just (Left ())           -> help (t + fromInteger k) ks mts
>             Just (Right (VarFac a))  -> help (t + k .* fromJust (lookup a axs)) ks mts
>             Just (Right (UnFac o `AppFac` m)) | Just lo <- linUnOp o ->
>                 linearise axs m mts $ \ m' mts' ->
>                     P.Exists $ \ y ->
>                         lo m' y :/\: help (t + k .* y) ks mts'
>             Just (Right (BinFac o `AppFac` m `AppFac` n)) | Just lo <- linBinOp o ->
>                  linearise axs m mts $ \ m' mts' ->
>                      linearise axs n mts' $ \ n' mts'' ->
>                          P.Exists $ \ y ->
>                              lo m' n' y :/\: help (t + k .* y) ks mts''        
>             _ -> case Map.lookup ys mts of
>                 Just n   -> help (t + k .* n) ks mts    
>                 Nothing  -> P.Forall (\ y -> help (t + k .* y) ks (Map.insert ys y mts))

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


