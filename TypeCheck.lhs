> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts, PatternGuards,
>              RankNTypes #-}

> module TypeCheck where

> import Control.Applicative hiding (Alternative)
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Maybe
> import qualified Data.Map as Map
> import Data.Foldable hiding (foldr, any)
> import Data.Traversable
> import Text.PrettyPrint.HughesPJ

> import qualified Data.Integer.Presburger as P
> import Data.Integer.Presburger (Formula (TRUE, FALSE, (:=:), (:<:), (:<=:), (:>:), (:>=:), (:\/:), (:/\:), (:=>:)))

> import BwdFwd
> import Kind 
> import Type
> import TyNum
> import Syntax
> import Context
> import Unify
> import Kit
> import Error
> import PrettyPrinter
> import PrettyContext
> import KindCheck


The |inst| function takes a name-mangling function (for modifying the
names of binders), a type definition (for use when introducing binders
into the context) and a type to instantiate. It instantiates
forall-binders with fresh variables to produce a rho-type, and writes
a list of predicates found.

> inst :: VarState -> (forall k. TyDef k) -> Type l ->
>             ContextualWriter [Predicate] t (Type l)
> inst vs d (TyApp (TyApp Arr a) t) =
>     TyApp (TyApp Arr a) <$> inst vs d t
> inst vs d (Bind All x k t) = do
>     beta <- fresh vs x k d
>     inst vs d (unbindTy beta t)
> inst vs d (Qual p t) = do
>     tell [p]
>     inst vs d t
> inst vs d t = return t


The |instS| function is like |inst|, but also takes a constraint
status, and stores the predicates in the context with the given
status.

> instS :: VarState -> CStatus -> (forall k. TyDef k) -> Type l ->
>              Contextual t (Type l)
> instS vs s d t = do
>     (ty, cs) <- runWriterT $ inst vs d t
>     modifyContext (<><< map (Constraint s) cs)
>     return ty

> specialise :: Type l -> Contextual t (Type l)
> specialise = instS (UserVar All) Given Fixed

> instantiate :: Type l -> Contextual t (Type l)
> instantiate = instS SysVar Wanted Hole


> existentialise :: (MonadState (ZipState t) m, FV (Type k)) =>
>                       m (Type k) -> m (Type k)
> existentialise m = do
>     modifyContext (:< Layer FunTop) -- hackish
>     ty <- m
>     modifyContext $ help (flip elemTarget ty)
>     return ty
>   where
>     help :: (forall k. Var () k -> Bool) -> Context -> Context
>     help isHole (g :< A (a := Hole))
>         | isHole a                   = help isHole g :< A (a := Hole)
>         | otherwise                  = help isHole g :< A (a := Exists)
>     help isHole (g :< Layer FunTop)  = g
>     help isHole (g :< e)             = help isHole g :< e


> generalise :: Type KSet -> [Alternative ()] -> Contextual t (Type KSet, [Alternative ()])
> generalise t ps = do
>     g <- getContext
>     (g', tps) <- help g (t, ps) []
>     putContext g'
>     return tps
>   where
>     help :: Context -> (Type KSet, [Alternative ()]) -> [Predicate] ->
>                 Contextual t (Context, (Type KSet, [Alternative ()]))
>     help g@(_ :< Layer FunTop)                tps hs = return (g, tps)
>     help g@(_ :< Layer (PatternTop _ _ _ _))  tps hs = return (g, tps)
>     help (g :< Layer (LamBody _ _))           tps hs = help g tps hs
>     help (g :< Layer GenMark)                 tps hs = return (g, tps)

>     help (g :< A (a@(FVar _ KNum) := Exists)) (t, ps) hs
>       | a <? t || a <? ps || a <? hs = case solveFor a hs of
>             Just n   -> replaceHelp g (t, ps) hs a (reifyNum n)
>             Nothing  | a <? t -> traceContext "oh no" >>
>                                     errBadExistential a t ps
>                      | otherwise -> help g (t, ps) (filter (not . (a <?)) hs)
>     help (g :< A (a := Exists)) (t, ps) hs
>       | a <? t     = errBadExistential a t ps
>       | otherwise  = help g (t, ps) hs
>     help (g :< A (a := Some d)) (t, ps) hs = replaceHelp g (t, ps) hs a d
>     help (g :< A (a := d)) (t, ps) hs
>       | a <? t || a <? ps || a <? hs = help g (Bind All (fogVar a) (varKind a) (bindTy a t), ps) hs
>     help (g :< A _)                  tps hs      = help g tps hs

>     help (g :< Constraint Given h)   tps hs      = help g tps (h:hs)
>     help (g :< Constraint Wanted p)  (t, ps) hs  =
>         help g (Qual p t, ps) hs

>     help g tps hs = erk $ "generalise: can't help " ++ renderMe g


>     replaceHelp :: Context -> (Type KSet, [Alternative ()]) -> [Predicate] ->
>         Var () l -> Type l -> Contextual t (Context, (Type KSet, [Alternative ()]))
>     replaceHelp g (t, ps) hs a d = do
>         let hs' = case a of
>                    FVar _ KNum -> map (fmap (replaceTy a d)) hs
>                    _           -> hs
>         help g (replaceTy a d t, map (replaceTypes a d) ps) hs'

>     solveFor :: Var () KNum -> [Predicate] -> Maybe NormalNum
>     solveFor a = getFirst . foldMap (First . maybeSolveFor a) . mapMaybe f
>       where  f (P EL m n)  = Just (normaliseNum (m - n))
>              f _           = Nothing


> layerStops :: TmLayer -> Maybe (TmLayer, [Predicate], [Predicate])
> layerStops FunTop                   = Just (FunTop, [], [])
> layerStops GenMark                  = Just (GenMark, [], [])
> layerStops (PatternTop s bs hs ps)  = Just (PatternTop s bs [] [], hs, ps)
> layerStops _                        = Nothing


> unifySolveConstraints :: Contextual t ()
> unifySolveConstraints = do
>     (g, ns) <- runWriter . collectEqualities <$> getContext
>     putContext g
>     traverse (uncurry unifyNum) ns
>     return ()
>   where
>     collectEqualities :: Context -> Writer [(Type KNum, Type KNum)] Context
>     collectEqualities B0 = return B0
>     collectEqualities (g :< Layer l) = case layerStops l of
>         Just _   -> return $ g :< Layer l
>         Nothing  -> (:< Layer l) <$> collectEqualities g
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
>     collect (g :< Layer l) hs ps = case layerStops l of
>         Nothing        -> collect g hs ps <:< Layer l
>         Just (l', ks, ws)  -> (g :< Layer l', collectHyps g (ks ++ hs), ws ++ ps)
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
>         help t ((TyApp (TyApp (BinOp o) m) n, k):ks) | Just lo <- linOp o =
>             linearise axs (normaliseNum m) $ \ m' ->
>             linearise axs (normaliseNum n) $ \ n' ->
>                 P.Exists $ \ y ->
>                     lo m' n' y :/\: help (t + fromInteger k * y) ks
>         help t ((_, k):ks)  = P.Forall (\ y -> help (t + fromInteger k * y) ks)

>     linOp :: BinOp -> Maybe (P.Term -> P.Term -> P.Term -> P.Formula)
>     linOp Max = Just $ \ m n y -> ((m :=: y) :/\: (m :>=: n))
>                                       :\/: ((n :=: y) :/\: (n :>=: m))
>     linOp Min = Just $ \ m n y -> ((m :=: y) :/\: (m :<=: n))
>                                       :\/: ((n :=: y) :/\: (n :<=: m))
>     linOp _ = Nothing

>     compToFormula :: Comparator -> P.Term -> P.Term -> P.Formula
>     compToFormula EL  = (:=:)
>     compToFormula LE  = (:<=:)
>     compToFormula LS  = (:<:)
>     compToFormula GE  = (:>=:)
>     compToFormula GR  = (:>:)

>     opToTerm :: BinOp -> Maybe (P.Term -> P.Term -> P.Term)
>     opToTerm Plus   = Just (+)
>     opToTerm Minus  = Just (-)
>     opToTerm Times  = Just (*)
>     opToTerm _      = Nothing




> subsCheck :: Sigma -> Sigma -> Contextual () ()
> subsCheck s t = do
>     t  <- specialise t
>     s  <- instantiate s
>     case (s, t) of
>         (TyApp (TyApp Arr s1) s2, _) -> do
>             (t1, t2) <- unifyFun t
>             subsCheck t1 s1
>             subsCheck s2 t2
>         (_, TyApp (TyApp Arr t1) t2) -> do
>             (s1, s2) <- unifyFun s
>             subsCheck t1 s1
>             subsCheck s2 t2
>         (Bind b1 x1 k1 t1, Bind b2 x2 k2 t2) | b1 == b2 ->
>           hetEq k1 k2 (do
>             a <- fresh SysVar x1 k1 Fixed
>             subsCheck (unbindTy a t1) (unbindTy a t2)
>            ) (fail "subsCheck: kind mismatch")
>         _ -> unify s t


> instSigma :: Sigma -> Maybe Rho -> Contextual () Rho
> instSigma s Nothing   = instantiate s
> instSigma s (Just r)  = subsCheck s r >> return r

> checkSigma :: Sigma -> STerm () -> Contextual () (Term ())
> checkSigma s e = inLocation (sep [text "when checking", nest 2 (prettyHigh e),
>                                   text "has type", nest 2 (prettyHigh (fogTy s))]) $ do
>     unifySolveConstraints
>     modifyContext (:< Layer GenMark)
>     s' <- specialise s
>     as <- getNames <$> getContext
>     t <- checkRho s' e
>     unifySolveConstraints
>     solveOrSuspend
>     g <- getContext
>     putContext =<< help as g []
>     return t
>   where
>     getNames :: Context -> [Ex (Var ())]
>     getNames (_ :< Layer GenMark) = []
>     getNames (g :< A (a := _)) = Ex a : getNames g
>     getNames (g :< e) = getNames g

>     help :: [Ex (Var ())] -> Context -> [Either AnyTyEntry Predicate] ->
>                 Contextual () Context
>     help [] (g :< Layer GenMark) h  = return $ g <><| h
>     help as (g :< Layer GenMark) h  = erk $ "checkSigma help: failed to squish "
>                                         ++ intercalate "," (map (\ e -> unEx e fogSysVar) as)
>     help as (g :< A (a := Fixed)) h
>         | a <? h     = erk $ "checkSigma help: fixed variable "
>                                 ++ renderMe (fogSysVar a)
>                                 ++ " occurred illegally in "
>                                 ++ intercalate ", " (map (either show (renderMe . fogSysPred)) h)
>         | otherwise  = help (delete (Ex a) as) g h
>     help as (g :< A (a := Some d)) h = help as g (map (rep a d) h)
>     help as (g :< A a) h                   = help as g (Left (TE a) : h)
>     help as (g :< Constraint Wanted p) h   = help as g (Right p : h) 
>     help as (g :< Constraint Given p) h    = help as g h
>     help as B0 h = error "checkSigma help: ran out of context"

>     g <><| h = g <><< map toEnt h
>     toEnt (Left (TE a)) = A a
>     toEnt (Right p)  = Constraint Wanted p

>     rep :: Var () k -> Type k -> Either AnyTyEntry Predicate
>                -> Either AnyTyEntry Predicate
>     rep a t (Left (TE (b := Some d))) =
>         Left (TE (b := Some (replaceTy a t d)))
>     rep a t (Left e) = Left e
>     rep a@(FVar _ KNum) t (Right p) =
>         Right (fmap (replaceTy a t) p)
>     rep a t (Right p) = Right p


> checkInfer :: Maybe Rho -> STerm () -> Contextual () (Term () ::: Rho)

> checkInfer mty (TmVar x) = do
>     sc  <- tyOf <$> lookupTmVar x
>     ty  <- instSigma sc mty
>     return $ TmVar x ::: ty

> checkInfer mty (TmCon c) = do
>     sc  <- lookupTmCon c
>     ty  <- instSigma sc mty
>     return $ TmCon c ::: ty

> checkInfer mty (TmInt k) = do
>     instSigma tyInteger mty
>     return $ TmInt k ::: tyInteger

> checkInfer mty (TmApp f (TmBrace n)) = do
>     f ::: fty  <- inferRho f   
>     case fty of
>         Bind Pi x KNum aty -> do
>             n   <- checkNumKind Pi B0 n
>             a   <- fresh SysVar "_n" KNum (Some n)
>             ty  <- instSigma (unbindTy a aty) mty
>             return $ TmApp f (TmBrace n) ::: ty
>         _ -> erk $ "Inferred type " ++ renderMe (fogSysTy fty) ++ " of " ++
>                  renderMe (fogSys f) ++ " is not a pi-type with numeric domain"

> checkInfer mty (TmApp f s) = do
>     f ::: fty   <- inferRho f
>     (dom, cod)  <- unifyFun fty
>     s           <- checkSigma dom s
>     instSigma cod mty
>     return $ TmApp f s ::: cod

> checkInfer (Just r) (Lam x t) = do
>     (dom, cod) <- unifyFun r
>     b <- withLayer (LamBody (x ::: dom) ()) $ checkRho cod t
>     return $ Lam x b ::: r

> checkInfer Nothing (Lam x t) = do
>     a <- unknownTyVar x KSet
>     b ::: ty <- withLayer (LamBody (x ::: a) ()) $ inferRho t
>     return $ Lam x b ::: a --> ty

> checkInfer (Just r@(Bind Pi x KNum ty)) (NumLam n t) = do
>     a <- fresh (UserVar Pi) n KNum Exists -- should this be |Fixed|?
>     b <- withLayer (LamBody (n ::: tyInteger) ()) $
>              checkSigma (unbindTy a ty) (rawCoerce t)
>     return $ NumLam n (bindTm a b) ::: r

> checkInfer (Just r) (NumLam n t) = erk $
>     "Type " ++ renderMe (fogSysTy r) ++
>       " is not a pi-type with numeric domain, so it does not accept " ++
>         renderMe (NumLam n t)

> checkInfer Nothing (NumLam n t) = do
>     a <- fresh (UserVar Pi) n KNum Exists -- should this be |Fixed|?
>     b ::: ty <- withLayer (LamBody (n ::: tyInteger) ()) $ inferRho (rawCoerce t)
>     return $ NumLam n (bindTm a b) ::: Bind Pi n KNum (bindTy a ty)

> checkInfer mty (Let ds t) = do
>     (ds, bs) <- checkLocalDecls ds
>     t ::: ty <- withLayer (LetBody bs ()) $
>                     checkInfer mty t
>     return $ Let ds t ::: ty

> checkInfer mty (t :? xty) = do
>     TK sc KSet  <- inferKind All B0 xty
>     t           <- checkSigma sc t
>     r           <- instSigma sc mty
>     return $ (t :? sc) ::: r

> checkInfer (Just r) (Case t as) = do
>     t ::: ty <- inferRho t
>     as <- traverse (checkCaseAlt ty r) as
>     return $ Case t as ::: r

> checkInfer Nothing (Case t as) = do
>     t ::: ty <- inferRho t
>     atys  <- traverse (inferCaseAlt ty) as
>     r     <- unknownTyVar "_r" KSet
>     let as ::: tys = unzipAsc atys
>     traverse (unify r) tys
>     return (Case t as ::: r)

> checkInfer mty (TmBrace n) = erk "Braces aren't cool"


-- This is horrible, please improve it

> checkCaseAlt :: Rho -> Rho -> SCaseAlternative () -> Contextual () (CaseAlternative ())
> checkCaseAlt sty resty c@(CaseAlt p mg t) =
>   inLocation (text ("in case alternative") <++> prettyHigh c) $
>   withLayer (PatternTop ("case" ::: error "womble") [] [] []) $ do
>     checkPat True (sty --> resty) (p :! P0) $ \ (xs, ex, vs, rty) -> do
>       mg <- traverse (checkGuard . rawCoerce) mg
>       t  <- checkRho rty (rawCoerce t)
>       unifySolveConstraints
>       solveConstraints
>       let t'   = renameTypes (renameVS vs) t
>           mg'  = fmap (renameTypes (renameVS vs)) mg
>       (_, [Alt (p :! P0) mg t]) <- generalise (TyCon "Fake" KSet) [Alt xs mg' t'] 
>                   -- to fix up variables
>       return $ CaseAlt p mg t

> inferCaseAlt :: Rho -> SCaseAlternative () -> Contextual () (CaseAlternative () ::: Rho)
> inferCaseAlt sty c@(CaseAlt p mg t) = do
>   resty <- unknownTyVar "_res" KSet
>   inLocation (text ("in case alternative") <++> prettyHigh c) $
>    withLayer (PatternTop ("case" ::: error "womble") [] [] []) $
>     checkPat True (sty --> resty) (p :! P0) $ \ (xs, ex, vs, rty) -> do
>       mg <- traverse (checkGuard . rawCoerce) mg
>       t  <- checkRho rty (rawCoerce t)
>       unifySolveConstraints
>       solveConstraints
>       let t'   = renameTypes (renameVS vs) t
>           mg'  = fmap (renameTypes (renameVS vs)) mg
>       (_, [Alt (p :! P0) mg t]) <- generalise (TyCon "Fake" KSet) [Alt xs mg' t'] 
>                   -- to fix up variables
>       return $ CaseAlt p mg t ::: resty



> declToBinding :: Declaration () -> [TmName ::: Sigma]
> declToBinding (SigDecl x ty)  = [x ::: ty]
> declToBinding _               = []

> withLayerExtract :: TmLayer -> (TmLayer -> a) -> Contextual () t -> Contextual () (t, a)
> withLayerExtract l f m = do
>     modifyContext (:< Layer l)
>     t <- m
>     (g, a) <- extract <$> getContext
>     putContext g
>     return (t, a)
>   where
>     extract (g :< Layer l') | matchLayer l l'  = (g, f l')
>     extract (g :< e)                           = (g' :< e, a) where (g', a) = extract g

>     matchLayer (PatternTop (x ::: _) _ _ _)
>                (PatternTop (y ::: _) _ _ _) = x == y
>     matchLayer FunTop FunTop = True
>     matchLayer (LamBody (x ::: _) ()) (LamBody (y ::: _) ()) = x == y
>     matchLayer (LetBody _ _) (LetBody _ _) = True
>     matchLayer (LetBindings _) (LetBindings _) = True
>     matchLayer _ _ = False

> withLayer :: TmLayer -> Contextual () t -> Contextual () t
> withLayer l m = fst <$> withLayerExtract l (const ()) m

> inferRho :: STerm () -> Contextual () (Term () ::: Rho)
> inferRho t =
>   inLocation (text "in inferred expression" <++> prettyHigh t) $
>     checkInfer Nothing t

> checkRho :: Rho -> STerm () -> Contextual () (Term ())
> checkRho ty t =
>   inLocation (text "in checked expression" <++> prettyHigh t) $
>     tmOf <$> checkInfer (Just ty) t




> checkLocalDecls :: [SDeclaration ()] -> Contextual () ([Declaration ()], Bindings)
> checkLocalDecls ds =
>     withLayerExtract (LetBindings Map.empty) (\ (LetBindings bs) -> bs) $ do
>         traverse makeBinding ds
>         Data.List.concat <$> traverse checkInferFunDecl ds  

> makeBinding :: SDeclaration () -> Contextual () ()
> makeBinding (SigDecl x ty) = inLocation (text $ "in binding " ++ x) $ do
>     TK ty' k <- inferKind All B0 ty
>     case k of
>         KSet  -> insertBinding x (Just ty', False)
>         _     -> errKindNotSet (fogKind k)
> makeBinding (FunDecl x _)     = return ()
> makeBinding (DataDecl _ _ _)  = return ()

> checkInferFunDecl :: SDeclaration () -> Contextual () [Declaration ()]
> checkInferFunDecl (FunDecl s []) =
>   inLocation (text $ "in declaration of " ++ s) $ erk $ "No alternative"
> checkInferFunDecl fd@(FunDecl s (p:ps)) = do
>     when (not (null ps) && isVarAlt p) $ errDuplicateTmVar s
>     mty <- optional $ lookupBinding s
>     case mty of
>         Just (_ ::: ty, False)  -> (\ x -> [x]) <$> checkFunDecl ty fd
>         Just (_, True) -> errDuplicateTmVar s
>         Nothing          -> do
>             (fd, ty) <- inferFunDecl fd
>             updateBinding s (Just ty, True)
>             return [SigDecl s ty, fd]
> checkInferFunDecl (SigDecl x _) = do
>     _ ::: ty <- fst <$> lookupBinding x
>     return [SigDecl x ty]

> inferFunDecl (FunDecl s pats) =
>   inLocation (text $ "in declaration of " ++ s) $ withLayer FunTop $ do
>     sty     <- unknownTyVar "_x" KSet
>     pattys  <- traverse (inferAlt (s ::: sty)) pats
>     let ptms ::: ptys = unzipAsc pattys
>     traverse (unify sty) ptys
>     (ty', ptms') <- generalise sty ptms
>     return (FunDecl s ptms', simplifyTy ty')

> checkFunDecl sty (FunDecl s pats) =
>   inLocation (text $ "in declaration of " ++ s) $ withLayer FunTop $ do
>         ptms <- traverse (checkAlt (s ::: sty)) pats
>         return $ FunDecl s ptms





> checkAlt :: String ::: Sigma -> SAlternative () -> Contextual () (Alternative ())
> checkAlt (s ::: sc) (Alt xs mg t) =
>   inLocation (text ("in alternative " ++ s) <++> prettyHigh (Alt xs mg t)) $
>   withLayer (PatternTop (s ::: sc) [] [] []) $ do
>     sty <- specialise sc
>     checkPat True sty xs $ \ (xs, ex, vs, rty) -> do
>       mg <- traverse (checkGuard . rawCoerce) mg
>       t  <- checkRho rty (rawCoerce t)
>       unifySolveConstraints
>       solveConstraints
>       let t'   = renameTypes (renameVS vs) t
>           mg'  = fmap (renameTypes (renameVS vs)) mg
>       (_, [p]) <- generalise (TyCon "Fake" KSet) [Alt xs mg' t'] 
>                   -- to fix up variables
>       return p

> inferAlt :: String ::: Sigma -> SAlternative () ->
>                 Contextual () (Alternative () ::: Rho)
> inferAlt (s ::: sc) (Alt xs mg t) =
>   inLocation (text ("in alternative " ++ s) <++> prettyHigh (Alt xs mg t)) $
>   withLayer (PatternTop (s ::: sc) [] [] []) $
>     inferPat (rawCoerce t) xs $ \ (xs, ex, vs, t ::: r, ty) -> do
>       mg <- traverse (checkGuard . rawCoerce) mg
>       unifySolveConstraints
>       solveOrSuspend
>       let t'   = renameTypes (renameVS vs) t
>           mg'  = fmap (renameTypes (renameVS vs)) mg
>       return $ Alt xs mg' t' ::: ty


> checkGuard :: SGuard () -> Contextual () (Guard ())
> checkGuard (NumGuard ps)  = NumGuard <$> traverse learnPred ps
>   where
>     learnPred p = do
>       p <- checkPredKind Pi B0 p
>       modifyContext (:< Constraint Given p)
>       return p
> checkGuard (ExpGuard t)   = ExpGuard <$> checkRho tyBool t

 
> checkPat :: Bool -> Rho -> SPatternList o a ->
>               (forall b x . (PatternList () b, Ext () b x, VarSuffix () b, Rho) -> Contextual () p) ->
>                 Contextual () p

> checkPat top ty P0 q = q (P0, E0, VS0, ty)

> checkPat top ty (PatVar v :! ps) q = do
>     (dom, cod) <- unifyFun ty
>     modifyContext (:< Layer (LamBody (v ::: dom) ()))
>     checkPat top cod ps $ \ (xs, ex, vs, r) ->
>         q (PatVar v :! xs, ex, vs, r)

> checkPat top ty (PatCon c as :! ps) q = do
>     (cty, dom, cod) <- inLocation (text "in pattern" <++> prettyHigh (PatCon c as)) $ do
>         (dom, cod) <- unifyFun ty
>         sc   <- lookupTmCon c
>         cty  <- existentialise $ instS SysVar Given Hole sc
>         unless (patLength as == args cty) $
>             errConUnderapplied c (args cty) (patLength as)
>         return (cty, dom, cod)
>     checkPat False cty as $ \ (ys, yex, yvs, s) -> do
>         unify dom s
>         checkPat top cod ps $ \ (xs, xex, xvs, r) ->
>             renameTypes2 (renameVS yvs) xex xs $ \ xex' xs' ->
>                 extComp yex xex' $ \ ex ->
>                     q (PatCon c ys :! xs', ex, error "checkPat vs", r)

> checkPat top ty (PatIgnore :! ps) q = do
>     (dom, cod) <- unifyFun ty
>     checkPat top cod ps $ \ (xs, ex, vs, r) ->
>         q (PatIgnore :! xs, ex, vs, r)

> checkPat top (Bind Pi x KNum t) (PatBraceK k :! ps) q = do
>     b        <- fresh SysVar x KNum (Some (TyInt k))
>     aty      <- instS (UserVar All) Given Fixed (unbindTy b t)
>     checkPat top aty ps $ \ (xs, ex, vs, r) -> 
>         q (PatBraceK k :! xs, ex, vs, r)

> checkPat top (Bind Pi x KNum t) (PatBrace a 0 :! ps) q = do
>     modifyContext (:< Layer (LamBody (a ::: tyInteger) ()))
>     b <- freshVar (UserVar Pi) a KNum
>     let  t'  = unbindTy b t
>          d   = if top || b `elemTarget` t'
>                    then Fixed
>                    else Exists
>     modifyContext (:< A (b := d))
>     aty      <- instS (UserVar All) Given Fixed t'
>     checkPat top aty ps $ \ (xs, ex, vs, r) ->
>       bindUn b ex vs xs $ \ ex' vs' xs' ->
>         extComp (EC E0) ex' $ \ ex'' ->
>           q (PatBrace a 0 :! xs', ex'', vs', r)

> checkPat top (Bind Pi x KNum t) (PatBrace a k :! ps) q = do
>     modifyContext (:< Layer (LamBody (a ::: tyInteger) ()))
>     b <- freshVar SysVar ("_" ++ x ++ "_" ++ a ++ "_" ++ "oo") KNum
>     let  t'  = unbindTy b t
>          d   = if top || b `elemTarget` t'
>                       then Fixed
>                       else Exists
>     am <- fresh (UserVar Pi) a KNum d
>     modifyContext (:< A (b := Some (TyVar am + TyInt k)))
>     modifyContext (:< Constraint Given (0 %<=% TyVar am))
>     aty      <- instS (UserVar All) Given Fixed t'
>     checkPat top aty ps $ \ (xs, ex, vs, r) -> 
>       bindUn am ex vs xs $ \ ex' vs' xs' ->
>         extComp (EC E0) ex' $ \ ex'' ->
>           q (PatBrace a k :! xs', ex'', vs', r)

> checkPat top ty (p :! _) _ =
>     erk $ "checkPat: couldn't match pattern " ++ renderMe p
>                ++ " against type " ++ renderMe (fogSysTy ty)



> inferPat :: STerm () -> SPatternList o a ->
>     (forall b x . (PatternList () b, Ext () b x, VarSuffix () b, Term () ::: Rho, Rho) -> Contextual () p) ->
>                 Contextual () p

> inferPat t P0 q = do
>     t ::: r <- inferRho t
>     q (P0, E0, VS0, t ::: r, r)

> inferPat top (PatVar v :! ps) q = do
>     a <- unknownTyVar "_a" KSet
>     modifyContext (:< Layer (LamBody (v ::: a) ()))
>     inferPat top ps $ \ (xs, ex, vs, tr, ty) -> 
>         q (PatVar v :! xs, ex, vs, tr, a --> ty)

> inferPat top (PatCon c as :! ps) q = do
>     cty <- inLocation (text "in pattern" <++> prettyHigh (PatCon c as)) $ do
>         sc   <- lookupTmCon c
>         cty  <- existentialise $ instS SysVar Given Hole sc
>         unless (patLength as == args cty) $
>             errConUnderapplied c (args cty) (patLength as)
>         return cty
>     checkPat False cty as $ \ (ys, yex, yvs, s) ->
>       inferPat top ps $ \ (xs, xex, xvs, tr, ty) ->
>         renameTypes2 (renameVS yvs) xex xs $ \ xex' xs' ->
>           extComp yex xex' $ \ ex ->
>             q (PatCon c ys :! xs', ex, error "inferPat vs", tr, s --> ty)

> inferPat top (PatIgnore :! ps) q = do
>     b <- unknownTyVar "_b" KSet
>     inferPat top ps $ \ (xs, ex, vs, tr, ty) ->
>         q (PatIgnore :! xs, ex, vs, tr, b --> ty)

> inferPat top (PatBrace a 0 :! ps) q = do
>     n <- fresh (UserVar Pi) a KNum Exists
>     modifyContext (:< Layer GenMark)
>     modifyContext (:< Layer (LamBody (a ::: tyInteger) ()))
>     inferPat top ps $ \ (xs, ex, vs, tr, ty) -> do
>         (ty', _) <- generalise ty []
>         bindUn n ex vs xs $ \ ex' vs' xs' ->
>           extComp (EC E0) ex' $ \ ex'' ->
>             q (PatBrace a 0 :! xs', ex'', vs', tr,
>                 Bind Pi a KNum (bindTy n ty'))

> inferPat top (p :! _) _ =
>     erk $ "inferPat: couldn't infer type of pattern " ++ renderMe p
