> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts, PatternGuards,
>              RankNTypes #-}

> module Language.Inch.Solver where

> import Control.Applicative hiding (Alternative)
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Maybe

> import qualified Data.Integer.Presburger as P
> import Data.Integer.Presburger (Formula (TRUE, FALSE, (:=:), (:<:), (:<=:), (:>:), (:>=:), (:\/:), (:/\:), (:=>:)), (.*))

> import Language.Inch.BwdFwd
> import Language.Inch.Kind 
> import Language.Inch.Type
> import Language.Inch.TyNum
> import Language.Inch.Context
> import Language.Inch.Unify
> import Language.Inch.Kit
> import Language.Inch.Error
> import Language.Inch.Check


> unifySolveConstraints :: Contextual ()
> unifySolveConstraints = do
>     (g, ns) <- runWriter . collectEqualities <$> getContext
>     putContext g
>     mapM_ (uncurry unifyNum) ns
>     return ()
>   where
>     collectEqualities :: Context -> Writer [(Type KNum, Type KNum)] Context
>     collectEqualities B0 = return B0
>     collectEqualities (g :< Layer l True)  = return $ g :< Layer l True
>     collectEqualities (g :< Layer l False) = (:< Layer l False) <$> collectEqualities g
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
>     collect (g :< Layer l True)   vs hs ps = (g :< Layer l True, vs', hs', ps')
>         where (vs', hs', ps') = collectHyps g vs hs ps
>     collect (g :< Layer l False)  vs hs ps = collect g vs hs ps <:< Layer l False
>     collect (g :< e) vs hs ps = collect g vs hs ps <:< e
>
>     collectHyps ::  Context -> [Var () KNum] -> [Predicate] -> [Predicate] ->
>                         ([Var () KNum], [Predicate], [Predicate])
>     collectHyps B0 vs hs ps = (vs, hs, ps)
>     collectHyps (g :< Constraint Given h) vs hs ps = collectHyps g vs (h:hs) ps
>     collectHyps (g :< A (a@(FVar _ KNum) := Some d)) vs hs ps =
>         collectHyps g vs (subsPreds a d hs) (subsPreds a d ps)
>     collectHyps (g :< A (a@(FVar _ KNum) := _)) vs hs ps | a <? (hs, ps) =
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
>         _   -> traceContext "halp" >> errCannotDeduce hs qs

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
>     elimEquations xs ys q = help [] ys q
>       where
>         help :: [Predicate] -> [Predicate] -> Predicate ->
>                     ([Var () KNum], [Predicate], Predicate)
>         help ohs []      p = (xs, ohs, p)
>         help ohs (h@(P EL m n):rs) p = case solveForAny (normaliseNum (n - m)) of
>             Just (a, t)  -> help [] (map (fmap (replaceTy a t')) (rs ++ ohs))
>                                 (fmap (replaceTy a t') p)
>               where t' = reifyNum t
>             Nothing      -> help (h:ohs) rs p
>         help ohs (h:rs) p = help (h:ohs) rs p


> toFormula :: [Var () KNum] -> [NormalPredicate] -> NormalPredicate -> P.Formula
> toFormula xs ys px = 

<  trace (unlines ["toFormula", "[" ++ intercalate "," (map fogSysVar vs) ++ "]","[" ++ intercalate "," (map (renderMe . fogSysPred . reifyPred) hs) ++ "]","(" ++ renderMe (fogSysPred $ reifyPred p) ++ ")"]) $

>   case trivialPred px of
>     Just True   -> TRUE
>     Just False  -> FALSE
>     Nothing -- | null ys && isSimple p  -> FALSE
>             | px `elem` ys            -> TRUE
>     Nothing     -> let r = convert xs []
>                    in {- trace ("result: " ++ show r) -} r
>                   
>   where
>     convert :: [Var () KNum] -> [(Var () KNum, P.Term)] -> P.Formula
>     convert []      axs = gogo axs ys Map.empty $ \ hs' mts' ->
>                              predToFormula axs px mts' $ \ p' _ ->
>                                  hs' :=>: p'
>     convert (v:vs)  axs = P.Forall (\ t -> convert vs ((v, t) : axs))
                
>     gogo :: [(Var () KNum, P.Term)] -> [NormalPredicate] -> Map Monomial P.Term ->
>                 (P.Formula -> Map Monomial P.Term -> P.Formula) -> P.Formula
>     gogo _   []      mts f = f TRUE mts
>     gogo axs (h:hs)  mts f = predToFormula axs h mts $ \ h' mts' ->
>                                  gogo axs hs mts' (\ x -> f (h' :/\: x))

>     predToFormula :: [(Var () KNum, P.Term)] -> NormalPredicate ->
>                          Map Monomial P.Term ->
>                          (P.Formula -> Map Monomial P.Term -> P.Formula) -> P.Formula
>     predToFormula axs (P c m n) mts f  = linearise axs m mts $ \ m' mts' ->
>                                                linearise axs n mts' $ \ n' mts'' ->
>                                                  f (compToFormula c m' n') mts''
>     predToFormula axs (p :=> q) mts f  = predToFormula axs p mts $ 
>         \ p' mts' -> predToFormula axs q mts' $ \ q' mts'' -> f (p' :=>: q') mts''

>     linearise ::  [(Var () KNum, P.Term)] -> NormalNum ->
>                     Map Monomial P.Term ->
>                     (P.Term -> Map Monomial P.Term -> P.Formula) -> P.Formula
>     linearise axs zs ms f = help 0 (Map.toList (elimNN zs)) ms
>       where
>         help :: P.Term -> [(Monomial, Integer)] ->
>                     Map Monomial P.Term -> P.Formula
>         help t []            mts = f t mts
>         help t ((fs, k):ks)  mts = case getLinearMono fs of
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
>             _ -> case Map.lookup fs mts of
>                 Just n   -> help (t + k .* n) ks mts    
>                 Nothing  -> P.Forall (\ y -> help (t + k .* y) ks (Map.insert fs y mts))

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


