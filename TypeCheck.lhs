> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts, PatternGuards,
>              RankNTypes #-}

> module TypeCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Maybe
> import qualified Data.Map as Map
> import Data.Foldable hiding (foldr)
> import Data.Traversable
> import Text.PrettyPrint.HughesPJ

> import qualified Data.Integer.Presburger as P

> import BwdFwd
> import TyNum
> import Kind 
> import Type
> import Num
> import Syntax
> import Context
> import Unify
> import Kit
> import Error
> import PrettyPrinter
> import PrettyContext
> import KindCheck


> numTy   = TyCon "Integer" KSet
> boolTy  = TyCon "Bool" KSet


The |inst| function takes a name-mangling function (for modifying the
names of binders), a type definition (for use when introducing binders
into the context) and a type to instantiate. It instantiates
forall-binders with fresh variables to produce a rho-type, and writes
a list of predicates found.

> inst :: VarState -> (forall k. TyDef k) -> Type l ->
>             ContextualWriter [NormalPredicate] t (Type l)
> inst vs d (TyApp (TyApp Arr a) t) =
>     TyApp (TyApp Arr a) <$> inst vs d t
> inst vs d (Bind All x k t) = do
>     beta <- fresh vs x k d
>     inst vs d (unbindTy beta t)
> inst vs d (Qual p t) = do
>     p' <- lift $ normalisePred p
>     tell [p']
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
> specialise = instS UserVar Given Fixed

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


> generalise :: Type k -> [Pattern] -> Contextual t (Type k, [Pattern])
> generalise t ps = do
>     g <- getContext
>     (g', tps) <- help g (t, ps)
>     putContext g'
>     return tps
>   where
>     help :: Context -> (Type k, [Pattern]) -> Contextual t (Context, (Type k, [Pattern]))
>     help g@(_ :< Layer FunTop)                tps = return (g, tps)
>     help g@(_ :< Layer (PatternTop _ _ _ _))  tps = return (g, tps)
>     help (g :< A (a := d)) (t, ps)
>       | a <? t || a <? ps  = case d of
>         Exists  -> traceContext "oh no" >> errBadExistential a t ps
>         Some d  -> help g (replaceTy a d t, map (replaceTypes a d) ps)
>         _       -> help g (Bind All (fogVar a) (varKind a) (bindTy a t), ps)
>     help (g :< Layer (LamBody _ _))  tps      = help g tps
>     help (g :< A _)                  tps      = help g tps
>     help (g :< Constraint Given _)   tps      = help g tps
>     help (g :< Constraint Wanted p)  (t, ps)  =
>         help g (Qual (reifyPred p) t, ps)
>     help g tps = erk $ "generalise: can't help " ++ renderMe g




> layerStops :: TmLayer -> Maybe (TmLayer, [NormalPredicate], [NormalPredicate])
> layerStops FunTop                   = Just (FunTop, [], [])
> layerStops GenMark                  = Just (GenMark, [], [])
> layerStops (PatternTop s bs hs ps)  = Just (PatternTop s bs [] [], hs, ps)
> layerStops _                        = Nothing


> unifySolveConstraints :: Contextual t ()
> unifySolveConstraints = do
>     (g, ns) <- runWriter . collectEqualities <$> getContext
>     putContext g
>     traverse (unifyZero F0) ns
>     return ()
>   where
>     collectEqualities :: Context -> Writer [NormalNum] Context
>     collectEqualities B0 = return B0
>     collectEqualities (g :< Layer l) = case layerStops l of
>         Just _   -> return $ g :< Layer l
>         Nothing  -> (:< Layer l) <$> collectEqualities g
>     collectEqualities (g :< Constraint Wanted (IsZero n)) = tell [n]
>         >> collectEqualities g
>     collectEqualities (g :< e) = (:< e) <$> collectEqualities g


> trySolveConstraints :: Contextual t ([NormalPredicate], [NormalPredicate])
> trySolveConstraints = do
>     g <- getContext
>     let (g', hs, ps) = collect g [] []
>     putContext g'
>     qs <- filterM (formulaic hs) ps
>     return (hs, qs)
>   where
>     formulaic hs p = (not . P.check) <$> toFormula hs p
>
>     collect :: Context -> [NormalPredicate] -> [NormalPredicate] ->
>                    (Context, [NormalPredicate], [NormalPredicate])
>     collect B0 hs ps = (B0, hs, ps)
>     collect (g :< Constraint Wanted p)  hs ps = collect g hs (p:ps)
>     collect (g :< Constraint Given h)   hs ps =
>         collect g (h:hs) ps <:< Constraint Given h
>     collect (g :< A e@(a@(FVar _ KNum) := Some d)) hs ps =
>         let  dn = normalNum (toNum d)
>         in   collect g (subsPreds a dn hs) (subsPreds a dn ps ) <:< A e
>     collect (g :< Layer l) hs ps = case layerStops l of
>         Nothing        -> collect g hs ps <:< Layer l
>         Just (l', ks, ws)  -> (g :< Layer l', collectHyps g (ks ++ hs), ws ++ ps)
>     collect (g :< e) hs ps = collect g hs ps <:< e
>
>     collectHyps B0 hs = hs
>     collectHyps (g :< Constraint Given h) hs = collectHyps g (h:hs)
>     collectHyps (g :< _) hs = collectHyps g hs

>     (g, a, b) <:< e = (g :< e, a, b)


> solveConstraints :: Contextual t ()
> solveConstraints = do
>     (hs, qs) <- trySolveConstraints
>     case qs of
>         []  -> return ()
>         _   -> errCannotDeduce hs qs

> solveOrSuspend :: Contextual t ()
> solveOrSuspend = want . snd =<< trySolveConstraints
>   where
>     want :: [NormalPredicate] -> Contextual t ()
>     want [] = return ()
>     want (p:ps)
>         | nonsense p  = errImpossiblePred p
>         | otherwise   = modifyContext (:< Constraint Wanted p)
>                                 >> want ps
>
>     nonsense :: NormalPredicate -> Bool
>     nonsense (IsZero n) = maybe False (/= 0) (getConstant n)
>     nonsense (IsPos  n) = maybe False (< 0)  (getConstant n)



> toFormula :: [NormalPredicate] -> NormalPredicate ->
>                  Contextual t P.Formula
> toFormula hs p = do
>     g <- getContext
>     let hs'  = map (expandPred g . reifyPred) hs
>         p'   = expandPred g (reifyPred p)
>     return $ convert (expandContext g) [] hs' p'
>   where
>     convert :: Context -> [(Var () KNum, P.Term)] -> [Predicate] ->
>                    Predicate -> P.Formula
>     convert B0 axs hs p =
>         foldr (P.:/\:) P.TRUE (map (predToFormula . apply axs) hs)
>             P.:=>: predToFormula (apply axs p)
>     convert (g :< A (a@(FVar _ KNum) := _)) axs hs p = 
>         P.Forall (\ x -> convert g ((a, x) : axs) hs p)
>     convert (g :< _) axs hs p = convert g axs hs p

>     apply :: [(Var () KNum, P.Term)] -> Predicate -> Pred P.Term
>     apply xs = bindPred (NumVar . fromJust . flip lookup xs)
>                
>     predToFormula :: Pred P.Term -> P.Formula
>     predToFormula (P c m n) = compToFormula c (numToTerm m) (numToTerm n)

>     compToFormula :: Comparator -> P.Term -> P.Term -> P.Formula
>     compToFormula EL  = (P.:=:)
>     compToFormula LE  = (P.:<=:)
>     compToFormula LS  = (P.:<:)
>     compToFormula GE  = (P.:>=:)
>     compToFormula GR  = (P.:>:)

>     numToTerm :: TyNum P.Term -> P.Term
>     numToTerm (NumConst k)  = fromInteger k
>     numToTerm (NumVar t)    = t
>     numToTerm (n :+: m)     = numToTerm n + numToTerm m
>     numToTerm (n :*: m)     = numToTerm n * numToTerm m
>     numToTerm (Neg n)       = - numToTerm n





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

> checkSigma :: Sigma -> STerm -> Contextual () Term
> checkSigma s e = do
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

>     help :: [Ex (Var ())] -> Context -> [Either AnyTyEntry NormalPredicate] ->
>                 Contextual () Context
>     help [] (g :< Layer GenMark) h  = return $ g <><| h
>     help as (g :< Layer GenMark) h  = erk $ "Bad as"
>     help as (g :< A (a := Fixed)) h
>         | a <? h     = erk "checkSigma help: bad h"
>         | otherwise  = help (delete (Ex a) as) g h
>     help as (g :< A (a := Some d)) h = help as g (map (rep a d) h)
>     help as (g :< A a) h                   = help as g (Left (TE a) : h)
>     help as (g :< Constraint Wanted p) h   = help as g (Right p : h) 
>     help as (g :< Constraint Given p) h    = help as g h
>     help as B0 h = error "checkSigma help: ran out of context"

>     g <><| h = g <><< map toEnt h
>     toEnt (Left (TE a)) = A a
>     toEnt (Right p)  = Constraint Wanted p

>     rep :: Var () k -> Type k -> Either AnyTyEntry NormalPredicate
>                -> Either AnyTyEntry NormalPredicate
>     rep a t (Left (TE (b := Some d))) =
>         Left (TE (b := Some (replaceTy a t d)))
>     rep a t (Left e) = Left e
>     rep a@(FVar _ KNum) t (Right p) =
>         Right (substNormPred a (normalNum $ toNum t) p)
>     rep a t (Right p) = Right p


> checkInfer :: Maybe Rho -> STerm -> Contextual () (Term ::: Rho)

> checkInfer mty (TmVar x) = do
>     sc  <- tyOf <$> lookupTmVar x
>     ty  <- instSigma sc mty
>     return $ TmVar x ::: ty

> checkInfer mty (TmCon c) = do
>     sc  <- lookupTmCon c
>     ty  <- instSigma sc mty
>     return $ TmCon c ::: ty

> checkInfer mty (TmInt k) = do
>     instSigma numTy mty
>     return $ TmInt k ::: numTy

> checkInfer mty (TmApp f (TmBrace n)) = do
>     f ::: fty  <- inferRho f   
>     case fty of
>         Bind Pi x KNum aty -> do
>             n   <- checkNumKind B0 n
>             a   <- fresh SysVar "_n" KNum (Some (TyNum n))
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

> checkInfer mty (Let ds t) = do
>     (ds, bs) <- checkLocalDecls ds
>     t ::: ty <- withLayer (LetBody bs ()) $
>                     checkInfer mty t
>     return $ Let ds t ::: ty

> checkInfer mty (t :? xty) = do
>     TK sc KSet  <- inferKind B0 xty
>     t           <- checkSigma sc t
>     r           <- instSigma sc mty
>     return $ (t :? sc) ::: r

> checkInfer mty (TmBrace n) = erk "Braces aren't cool"


> declToBinding :: Declaration -> [TmName ::: Sigma]
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

> inferRho :: STerm -> Contextual () (Term ::: Rho)
> inferRho t =
>   inLocation (text "in inferred expression" <+> prettyHigh t) $
>     checkInfer Nothing t

> checkRho :: Rho -> STerm -> Contextual () Term
> checkRho ty t =
>   inLocation (text "in checked expression" <+> prettyHigh t) $
>     tmOf <$> checkInfer (Just ty) t




> checkLocalDecls :: [SDeclaration] -> Contextual () ([Declaration], Bindings)
> checkLocalDecls ds =
>     withLayerExtract (LetBindings Map.empty) (\ (LetBindings bs) -> bs) $ do
>         traverse makeBinding ds
>         Data.List.concat <$> traverse checkInferFunDecl ds  

> makeBinding :: SDeclaration -> Contextual () ()
> makeBinding (SigDecl x ty) = inLocation (text $ "in binding " ++ x) $ do
>     TK ty' k <- inferKind B0 ty
>     case k of
>         KSet  -> insertBinding x (Just ty')
>         _     -> errKindNotSet (fogKind k)
> makeBinding (FunDecl x _) = insertBinding x Nothing <|> return ()
> makeBinding (DataDecl _ _ _) = return ()

> checkInferFunDecl :: SDeclaration -> Contextual () [Declaration]
> checkInferFunDecl (FunDecl s []) =
>   inLocation (text $ "in declaration of " ++ s) $ erk $ "No alternative"
> checkInferFunDecl fd@(FunDecl s (p:ps)) = do
>     when (not (null ps) && isVarPat p) $ erk $ "Multiple bindings for variable " ++ s
>     mty <- optional $ lookupBinding s
>     case mty of
>         Just (_ ::: ty)  -> (\ x -> [x]) <$> checkFunDecl ty fd
>         Nothing          -> do
>             (fd, ty) <- inferFunDecl fd
>             updateBinding s (Just ty)
>             return [SigDecl s ty, fd]
> checkInferFunDecl (SigDecl x _) = do
>     _ ::: ty <- lookupBinding x
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





> checkAlt :: String ::: Sigma -> SPattern -> Contextual () Pattern
> checkAlt (s ::: sc) (Pat xs g t) =
>   inLocation (text ("in alternative " ++ s) <+> prettyHigh (Pat xs g t)) $
>   withLayer (PatternTop (s ::: sc) [] [] []) $ do
>     sty <- specialise sc
>     (xs, rty) <- checkPat True sty xs
>     g <- traverse checkGuard g
>     t  <- checkRho rty t
>     unifySolveConstraints
>     solveConstraints
>     (_, [p]) <- generalise Arr [Pat xs g t] -- to fix up variables
>     return p

> inferAlt :: String ::: Sigma -> SPattern ->
>                 Contextual () (Pattern ::: Rho)
> inferAlt (s ::: sc) (Pat xs g t) =
>   inLocation (text ("in alternative " ++ s) <+> prettyHigh (Pat xs g t)) $
>   withLayer (PatternTop (s ::: sc) [] [] []) $ do
>     (xs, t ::: r, ty) <- inferPat t xs
>     g <- traverse checkGuard g
>     unifySolveConstraints
>     solveOrSuspend
>     return $ Pat xs g t ::: ty


> checkGuard :: SGuard -> Contextual () Guard
> checkGuard (NumGuard ps)  = NumGuard <$> traverse learnPred ps
>   where
>     learnPred p = do
>       p <- checkPredKind B0 p
>       np <- normalisePred p
>       modifyContext (:< Constraint Given np)
>       return p
> checkGuard (ExpGuard t)   = ExpGuard <$> checkRho boolTy t

 
> checkPat :: Bool -> Rho -> [SPatternTerm] ->
>                 Contextual () ([PatternTerm], Rho)

> checkPat top ty [] = return ([], ty)

> checkPat top ty (PatVar v : ps) = do
>     (dom, cod) <- unifyFun ty
>     modifyContext (:< Layer (LamBody (v ::: dom) ()))
>     (xs, r) <- checkPat top cod ps
>     return (PatVar v : xs, r)

> checkPat top ty (PatCon c as : ps) =
>   inLocation (text "in pattern" <+> prettyHigh (PatCon c as)) $ do
>     (dom, cod) <- unifyFun ty
>     sc   <- lookupTmCon c
>     cty  <- existentialise $ instS SysVar Given Hole sc
>     unless (length as == args cty) $
>         errConUnderapplied c (args cty) (length as)
>     (ys, s)  <- checkPat False cty as
>     unify dom s
>     (xs, r) <- checkPat top cod ps
>     return (PatCon c ys : xs, r)

> checkPat top ty (PatIgnore : ps) = do
>     (dom, cod) <- unifyFun ty
>     (xs, r) <- checkPat top cod ps
>     return (PatIgnore : xs, r)

> checkPat top (Bind Pi x KNum t) (PatBrace Nothing k : ps) = do
>     b        <- fresh SysVar x KNum (Some (TyNum (NumConst k)))
>     aty      <- instS UserVar Given Fixed (unbindTy b t)
>     (xs, r)  <- checkPat top aty ps
>     return (PatBrace Nothing k : xs, r)

> checkPat top (Bind Pi x KNum t) (PatBrace (Just a) 0 : ps) = do
>     modifyContext (:< Layer (LamBody (a ::: numTy) ()))
>     b <- freshVar UserVar a KNum
>     let  t'  = unbindTy b t
>          d   = if top || b `elemTarget` t'
>                    then Fixed
>                    else Exists
>     modifyContext (:< A (b := d))
>     aty      <- instS UserVar Given Fixed t'
>     (xs, r)  <- checkPat top aty ps
>     return (PatBrace (Just a) 0 : xs, r)

> checkPat top (Bind Pi x KNum t) (PatBrace (Just a) k : ps) = do
>     modifyContext (:< Layer (LamBody (a ::: numTy) ()))
>     b <- freshVar SysVar ("_" ++ x ++ "_" ++ a ++ "_" ++ "oo") KNum
>     let  t'  = unbindTy b t
>          d   = if top || b `elemTarget` t'
>                       then Fixed
>                       else Exists
>     am <- fresh UserVar a KNum d
>     modifyContext (:< A (b := Some (TyNum (NumVar am + NumConst k))))
>     modifyContext (:< Constraint Given (IsPos (mkVar am)))
>     aty      <- instS UserVar Given Fixed t'
>     (xs, r)  <- checkPat top aty ps
>     return (PatBrace (Just a) k : xs, r)

> checkPat top ty (p : _) =
>     erk $ "checkPat: couldn't match pattern " ++ renderMe p
>                ++ " against type " ++ renderMe (fogSysTy ty)



> inferPat :: STerm -> [SPatternTerm] ->
>                 Contextual () ([PatternTerm], Term ::: Rho, Rho)

> inferPat t [] = do
>     t ::: r <- inferRho t
>     return ([], t ::: r, r)

> inferPat top (PatVar v : ps) = do
>     a <- unknownTyVar "_a" KSet
>     modifyContext (:< Layer (LamBody (v ::: a) ()))
>     (xs, tr, ty) <- inferPat top ps
>     return (PatVar v : xs, tr, a --> ty)

> inferPat top (PatCon c as : ps) =
>   inLocation (text "in pattern" <+> prettyHigh (PatCon c as)) $ do
>     sc   <- lookupTmCon c
>     cty  <- existentialise $ instS SysVar Given Hole sc
>     unless (length as == args cty) $
>         errConUnderapplied c (args cty) (length as)
>     (ys, s) <- checkPat False cty as
>     (xs, tr, ty)  <- inferPat top ps
>     return (PatCon c ys : xs, tr, s --> ty)

> inferPat top (PatIgnore : ps) = do
>     b <- unknownTyVar "_b" KSet
>     (xs, tr, ty) <- inferPat top ps
>     return (PatIgnore : xs, tr, b --> ty)

> inferPat top (PatBrace (Just a) 0 : ps) = do
>     n <- fresh UserVar a KNum Hole
>     modifyContext (:< Layer (LamBody (a ::: numTy) ()))
>     (xs, tr, ty) <- inferPat top ps
>     return (PatBrace (Just a) 0 : xs, tr,
>         Bind Pi a KNum (bindTy n ty))

> inferPat top (p : _) =
>     erk $ "inferPat: couldn't infer type of pattern " ++ renderMe p
