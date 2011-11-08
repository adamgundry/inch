> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts, PatternGuards,
>              RankNTypes #-}

> module Language.Inch.TypeCheck where

> import Control.Applicative hiding (Alternative)
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Maybe
> import qualified Data.Map as Map
> import Data.Foldable hiding (foldr, any, mapM_)
> import Data.Traversable
> import Text.PrettyPrint.HughesPJ

> import Language.Inch.BwdFwd
> import Language.Inch.Kind 
> import Language.Inch.Type
> import Language.Inch.TyNum
> import Language.Inch.Syntax
> import Language.Inch.Context
> import Language.Inch.Unify
> import Language.Inch.Kit
> import Language.Inch.Error
> import Language.Inch.PrettyPrinter
> import Language.Inch.KindCheck
> import Language.Inch.Solver
> import Language.Inch.Check



The |inst| function takes a name-mangling function (for modifying the
names of binders), a type definition (for use when introducing binders
into the context) and a type to instantiate. It instantiates
forall-binders with fresh variables to produce a rho-type, and writes
a list of predicates found.

> inst :: VarState -> (forall k. TyDef k) -> Type l ->
>             ContextualWriter [Type KConstraint] (Type l)
> inst vs d (TyApp (TyApp Arr a) t) =
>     TyApp (TyApp Arr a) <$> inst vs d t
> inst vs d (Bind All x k t) = do
>     beta <- fresh vs x k d
>     inst vs d (unbindTy beta t)
> inst vs d (Qual p t) = do
>     tell [p]
>     inst vs d t
> inst _ _ t = return t


The |instS| function is like |inst|, but also takes a constraint
status, and stores the predicates in the context with the given
status.

> instS :: VarState -> CStatus -> (forall k. TyDef k) -> Type l ->
>              Contextual (Type l)
> instS vs s d t = do
>     (ty, cs) <- runWriterT $ inst vs d t
>     modifyContext (<><< map (Constraint s) cs)
>     return ty

> specialise :: Type l -> Contextual (Type l)
> specialise = instS (UserVar All) Given Fixed

> instantiate :: Type l -> Contextual (Type l)
> instantiate = instS SysVar Wanted Hole


> existentialise :: (MonadState ZipState m, FV (Type k) ()) =>
>                       m (Type k) -> m (Type k)
> existentialise m = do
>     modifyContext (:< Layer FunTop False) -- hackish
>     ty <- m
>     modifyContext $ help (flip elemTarget ty)
>     return ty
>   where
>     help :: (forall k. Var () k -> Bool) -> Context -> Context
>     help isHole (g :< A (a := Hole))
>         | isHole a                     = help isHole g :< A (a := Hole)
>         | otherwise                    = help isHole g :< A (a := Exists)
>     help _      (g :< Layer FunTop _)  = g
>     help isHole (g :< e)               = help isHole g :< e
>     help _      B0                     = error "existentialise: ran out of context"


> generalise :: (FV (t OK ()) (), TravTypes t) => Type KSet -> [t OK ()] ->
>                   Contextual (Type KSet, [t OK ()])
> generalise u qs = do
>     g <- getContext
>     (g', tps) <- help g (u, qs) []
>     putContext g'
>     return tps
>   where
>     help :: (FV (t OK ()) (), TravTypes t) =>  Context ->
>                 (Type KSet, [t OK ()]) -> [Type KConstraint] ->
>                     Contextual (Context, (Type KSet, [t OK ()]))
>     help (g :< Layer l True)   tps _ = return (g :< Layer l True, tps)
>     help (g :< Layer l False)  tps hs = (<:< Layer l False) <$> help g tps hs 

>     help (g :< A (a@(FVar _ KNum) := Exists)) (t, ps) hs
>       | a <? (t, ps, hs) = case solveForLots a hs of
>             Just n   -> replaceHelp g (t, ps) hs a (reifyNum n)
>             Nothing  | a <? t -> traceContext "oh no" >>
>                                     errBadExistential a t
>                      | otherwise -> help g (t, ps) (filter (not . (a <?)) hs)
>     help (_ :< A (a := Exists)) (t, ps) hs
>       | a <? (t, ps, hs)     = errBadExistential a t
>     help (g :< A (a := Some d)) (t, ps) hs = replaceHelp g (t, ps) hs a d
>     help (g :< A (a := _)) (t, ps) hs
>       | a <? (t, ps, hs) = help g (Bind All (fogVar a) (varKind a) (bindTy a t), ps) hs
>     help (g :< A _)                  tps hs      = help g tps hs

>     help (g :< Constraint Given h)   tps hs      = help g tps (h:hs)
>     help (g :< Constraint Wanted p)  (t, ps) hs  =
>         help g (Qual p t, ps) hs

>     help _ _ _ = erk $ "generalise: hit empty context"

            
>     (<:<) :: (Context, t) -> Entry -> (Context, t)
>     (g, x) <:< e = (g :< e, x)


>     replaceHelp :: (FV (t OK ()) (), TravTypes t) => Context ->
>                        (Type KSet, [t OK ()]) -> [Type KConstraint] ->
>                            Var () l -> Type l ->
>                                Contextual (Context, (Type KSet, [t OK ()]))
>     replaceHelp g (t, ps) hs a d =
>         help g (replaceTy a d t, map (replaceTypes a d) ps) (map (replaceTy a d) hs)

>     solveForLots :: Var () KNum -> [Type KConstraint] -> Maybe NormalNum
>     solveForLots a = getFirst . foldMap (First . maybeSolveFor a) . mapMaybe f
>       where  f (TyComp EL `TyApp` m `TyApp` n)  = Just (normaliseNum (m - n))
>              f _           = Nothing


> subsCheck :: Sigma -> Sigma -> Contextual ()
> subsCheck s t = do
>     t'  <- specialise t
>     s'  <- instantiate s
>     case (s', t') of
>         (TyApp (TyApp Arr s1) s2, _) -> do
>             (t1, t2) <- unifyFun t'
>             subsCheck t1 s1
>             subsCheck s2 t2
>         (_, TyApp (TyApp Arr t1) t2) -> do
>             (s1, s2) <- unifyFun s'
>             subsCheck t1 s1
>             subsCheck s2 t2
>         (Bind Pi x KNum t1, Bind Pi _ KNum t2) -> do
>             a <- fresh SysVar x KNum Fixed
>             subsCheck (unbindTy a t1) (unbindTy a t2)
>         _ -> unify s' t'


> instSigma :: Sigma -> Maybe Rho -> Contextual Rho
> instSigma s Nothing   = instantiate s
> instSigma s (Just r)  = subsCheck s r >> return r




> inferRho :: STerm () -> Contextual (Term () ::: Rho)
> inferRho t =
>   inLocation (text "in inferred expression" <++> prettyHigh t) $
>     checkInfer Nothing t

> checkRho :: Rho -> STerm () -> Contextual (Term ())
> checkRho ty t =
>   inLocation (text "in checked expression" <++> prettyHigh t) $
>     tmOf <$> checkInfer (Just ty) t




> checkSigma :: Sigma -> STerm () -> Contextual (Term ())
> checkSigma s e = inLocation (sep [text "when checking", nest 2 (prettyHigh e),
>                                   text "has type", nest 2 (prettyHigh (fogTy s))]) $ do
>     unifySolveConstraints
>     modifyContext (:< Layer GenMark True)
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
>     getNames (_ :< Layer GenMark _)  = []
>     getNames (g :< A (a := _))       = Ex a : getNames g
>     getNames (g :< _)                = getNames g
>     getNames B0                      = error "getNames: ran out of context"

>     help :: [Ex (Var ())] -> Context -> [Entry] -> Contextual Context
>     help [] (g :< Layer GenMark _) h  = return $ g <><| h
>     help as (_ :< Layer GenMark _) _  = erk $ "checkSigma help: failed to squish "
>                                         ++ intercalate "," (map (\ x -> unEx x fogSysVar) as)
>     help _  (_ :< Layer l _)       _  = error $ "checkSigma.help: hit bad layer " ++ show l
>     help as (g :< A (a := Fixed)) h = case suppress a h of
>         Just h'  -> help (delete (Ex a) as) g h'
>         Nothing  -> traceContext "noooooooooo" >> (erk $ "checkSigma help: fixed variable "
>                                 ++ renderMe (fogSysVar a)
>                                 ++ " occurred illegally in "
>                                 ++ show (fsepPretty h))
>     help as (g :< A (a := Some d)) h = help as g (fmap (replaceTyEntry a d) h)
>     help as (g :< A a) h                   = help as g (A a : h)
>     help as (g :< Constraint Wanted p) h   = help as g (Constraint Wanted p : h) 
>     help as (g :< Constraint Given p) h    = help as g (map (abstract p) h)
>     help _  B0 _ = error "checkSigma help: ran out of context"

>     abstract p  (Constraint s q)  = Constraint s (Qual p q)
>     abstract _  x                 = x

>     (<><|) :: Context -> [Entry] -> Context
>     g <><| [] = g
>     g <><| (x:xs) = (g :< x) <><| xs

>     suppress :: Var () k -> [Entry] -> Maybe [Entry]
>     suppress _ [] = return []
>     suppress a (x : xs) | not (a <? x) = (x :) <$> suppress a xs
>     suppress a@(FVar _ KNum) (Constraint Wanted p : es) = suppressPred a p >>=
>         \ p' -> (Constraint Wanted p' :) <$> suppress a es
>     suppress _ _ = Nothing

>     suppressPred :: Var () KNum -> Type KConstraint -> Maybe (Type KConstraint)
>     suppressPred a (Qual p q) | a <? p     = suppressPred a q
>                               | otherwise  = Qual p <$> suppressPred a q
>     suppressPred a p | a <? p     = Nothing
>                      | otherwise  = Just p




> checkInfer :: Maybe Rho -> STerm () -> Contextual (Term () ::: Rho)

> checkInfer mty (TmVar x) = do
>     sc  <- tyOf <$> lookupTmVar x
>     ty  <- instSigma sc mty
>     return $ TmVar x ::: ty

> checkInfer mty (TmCon c) = do
>     sc  <- lookupTmCon c
>     ty  <- instSigma sc mty
>     return $ TmCon c ::: ty

> checkInfer mty (TmInt k) = do
>     _ <- instSigma tyInteger mty
>     return $ TmInt k ::: tyInteger

> checkInfer mty (CharLit c) = do
>     _ <- instSigma tyChar mty
>     return $ CharLit c ::: tyChar

> checkInfer mty (StrLit s) = do
>     _ <- instSigma tyString mty
>     return $ StrLit s ::: tyString

> checkInfer mty (TmUnOp o) = do
>     _ <- instSigma (tyInteger --> tyInteger) mty
>     return $ TmUnOp o ::: tyInteger --> tyInteger

> checkInfer mty (TmBinOp o) = do
>     _ <- instSigma (tyInteger --> tyInteger --> tyInteger) mty
>     return $ TmBinOp o ::: tyInteger --> tyInteger --> tyInteger

> checkInfer mty (TmComp c) = do
>     _ <- instSigma (tyInteger --> tyInteger --> tyBool) mty
>     return $ TmComp c ::: tyInteger --> tyInteger --> tyBool

> checkInfer mty (TmApp f (TmBrace n)) = do
>     f' ::: fty  <- inferRho f   
>     case fty of
>         Bind Pi _ KNum aty -> do
>             n'   <- checkNumKind Pi B0 n
>             a   <- fresh SysVar "_n" KNum (Some n')
>             ty  <- instSigma (unbindTy a aty) mty
>             return $ TmApp f' (TmBrace n') ::: ty
>         _ -> erk $ "Inferred type " ++ renderMe (fogSysTy fty) ++ " of " ++
>                  renderMe (fogSys f') ++ " is not a pi-type with numeric domain"

> checkInfer mty (TmApp f s) = do
>     f' ::: fty  <- inferRho f
>     (dom, cod)  <- unifyFun fty
>     s'          <- checkSigma dom s
>     _ <- instSigma cod mty
>     return $ TmApp f' s' ::: cod

> checkInfer (Just r) (Lam x t) = do
>     (dom, cod) <- unifyFun r
>     b <- withLayer False False (LamBody (x ::: dom)) $ checkRho cod t
>     return $ Lam x b ::: r

> checkInfer Nothing (Lam x t) = do
>     a <- unknownTyVar x KSet
>     b ::: ty <- withLayer False False (LamBody (x ::: a)) $ inferRho t
>     return $ Lam x b ::: a --> ty

> checkInfer (Just r@(Bind Pi _ KNum ty)) (NumLam n t) = do
>     a <- fresh (UserVar Pi) n KNum Fixed -- should this be |Exists|?
>     b <- withLayer False False (LamBody (n ::: tyInteger)) $
>              checkSigma (unbindTy a ty) (rawCoerce t)
>     return $ NumLam n (bindTm a b) ::: r

> checkInfer (Just r) (NumLam n t) = erk $
>     "Type " ++ renderMe (fogSysTy r) ++
>       " is not a pi-type with numeric domain, so it does not accept " ++
>         renderMe (NumLam n t)

> checkInfer Nothing (NumLam n t) = do
>     a <- fresh (UserVar Pi) n KNum Fixed -- should this be |Exists|?
>     b ::: ty <- withLayer False False (LamBody (n ::: tyInteger)) $ inferRho (rawCoerce t)
>     return $ NumLam n (bindTm a b) ::: Bind Pi n KNum (bindTy a ty)

> checkInfer mty (Let ds t) = do
>     (ds', bs) <- checkLocalDecls ds
>     t' ::: ty <- withLayer False False (LetBody bs) $
>                     checkInfer mty t
>     return $ Let ds' t' ::: ty

> checkInfer mty (t :? xty) = do
>     sc  <- checkKindSet All B0 xty
>     t'  <- checkSigma sc t
>     r   <- instSigma sc mty
>     return $ (t' :? sc) ::: r

> checkInfer (Just r) (Case t as) = do
>     t' ::: ty <- inferRho t
>     as' <- traverse (checkCaseAlt ty r) as
>     return $ Case t' as' ::: r

> checkInfer Nothing (Case t as) = do
>     t' ::: ty    <- inferRho t
>     as' ::: tys  <- unzipAsc <$> traverse (inferCaseAlt ty) as
>     r            <- unifyList tys
>     return (Case t' as' ::: r)

> checkInfer _ (TmBrace _) = erk "Braces aren't cool"


> checkLocalHypotheses :: TmLayer -> Contextual ()
> checkLocalHypotheses l = modifyContext (help False)
>   where
>     help :: Bool -> Context -> Context
>     help z (g :< Layer l' b) | matchLayer l l'  = g :< Layer l' (b || z)
>     help _ (g :< Layer l' True)                 = g :< Layer l' True
>     help _ (g :< e@(Constraint Given _))        = help True g :< e
>     help z (g :< e)                             = help z g :< e
>     help _ B0                                   = error "checkLocalHypotheses: empty!"

-- This is horrible, please improve it

> checkCaseAlt :: Rho -> Rho -> SCaseAlternative () -> Contextual (CaseAlternative ())
> checkCaseAlt sty resty c@(CaseAlt p gt) =
>   inLocation (text "in case alternative" <++> prettyHigh c) $
>   withLayer False True CaseTop $ do
>     ca <- checkPat True (sty --> resty) (p :! P0) $ \ (p' :! P0, _, vs, rty) -> do
>       checkLocalHypotheses CaseTop
>       gt' <- checkGuardTerms rty (rawCoerce gt)
>       return $ CaseAlt p' (renameTypes (renameVS vs) gt')
>     unifySolveConstraints
>     solveConstraints
>     return ca

> inferCaseAlt :: Rho -> SCaseAlternative () -> Contextual (CaseAlternative () ::: Rho)
> inferCaseAlt sty c@(CaseAlt p gt) = do
>   resty <- unknownTyVar "_r" KSet
>   inLocation (text "in case alternative" <++> prettyHigh c) $
>    withLayer False True CaseTop $ do
>     ca <- checkPat True (sty --> resty) (p :! P0) $ \ (p' :! P0, _, vs, rty) -> do
>       checkLocalHypotheses CaseTop
>       gt' <- checkGuardTerms rty (rawCoerce gt)
>       return $ CaseAlt p' (renameTypes (renameVS vs) gt')
>     return $ ca ::: resty


> checkLocalDecls :: [SDeclaration ()] -> Contextual ([Declaration ()], Bindings)
> checkLocalDecls ds =
>     withLayerExtract False False (LetBindings Map.empty) letBindings $ do
>         mapM_ (makeBinding False) ds
>         Data.List.concat <$> traverse checkInferFunDecl ds  

> makeBinding :: Bool -> SDeclaration () -> Contextual ()
> makeBinding defd (SigDecl x ty) = inLocation (text $ "in binding " ++ x) $ do
>     bs <- tyVarNamesInScope
>     TK ty' k <- inferKind All B0 (wrapForall bs ty)
>     case k of
>         KSet  -> insertBinding x (Just ty', defd)
>         _     -> errKindNotSet (fogKind k)
> makeBinding _ (FunDecl _ _)       = return ()
> makeBinding _ (DataDecl _ _ _ _)  = return ()

> checkInferFunDecl :: SDeclaration () -> Contextual [Declaration ()]
> checkInferFunDecl (FunDecl s []) =
>   inLocation (text $ "in declaration of " ++ s) $ erk $ "No alternative"
> checkInferFunDecl (FunDecl s (p:ps)) = do
>     when (not (null ps) && isVarAlt p) $ errDuplicateTmVar s
>     mty <- optional $ lookupBinding s
>     case mty of
>         Just (_ ::: ty, False)  -> (\ x -> [x]) <$> checkFunDecl ty s (p:ps)
>         Just (_, True) -> errDuplicateTmVar s
>         Nothing          -> do
>             (fd, ty) <- inferFunDecl s (p:ps)
>             updateBinding s (Just ty, True)
>             return [SigDecl s ty, fd]
> checkInferFunDecl (SigDecl x _) = do
>     _ ::: ty <- fst <$> lookupBinding x
>     return [SigDecl x ty]
> checkInferFunDecl (DataDecl _ _ _ _) = error "checkInferFunDecl: that's a data declaration"

> inferFunDecl :: String -> [SAlternative ()] -> Contextual (Declaration (), Type KSet)
> inferFunDecl s pats =
>   inLocation (text $ "in declaration of " ++ s) $ withLayer True True FunTop $ do
>     sty     <- unknownTyVar "_x" KSet
>     pattys  <- traverse (inferAlt (s ::: sty)) pats
>     let ptms ::: ptys = unzipAsc pattys
>     mapM_ (unify sty) ptys
>     (ty', ptms') <- generalise sty ptms
>     return (FunDecl s ptms', simplifyTy ty')

> checkFunDecl :: Sigma -> String -> [SAlternative ()] -> Contextual (Declaration ())
> checkFunDecl sty s pats =
>   inLocation (text $ "in declaration of " ++ s) $ withLayer True True FunTop $ do
>         ptms <- traverse (checkAlt (s ::: sty)) pats
>         (_, ptms') <- generalise (TyCon "Fake" KSet) ptms
>         return $ FunDecl s ptms'





> checkAlt :: String ::: Sigma -> SAlternative () -> Contextual (Alternative ())
> checkAlt (s ::: sc) (Alt xs gt) =
>   inLocation (text "in alternative" <++> (text s <+> prettyHigh (Alt xs gt))) $
>   withLayer True True (PatternTop (s ::: sc)) $ do
>     sty <- specialise sc
>     checkPat True sty xs $ \ (xs', _, vs, rty) -> do
>       gt' <- checkGuardTerms rty (rawCoerce gt)
>       return $ Alt xs' (renameTypes (renameVS vs) gt')


> inferAlt :: String ::: Sigma -> SAlternative () ->
>                 Contextual (Alternative () ::: Rho)
> inferAlt (s ::: sc) (Alt xs gt) =
>   inLocation (text "in alternative" <++> (text s <+> prettyHigh (Alt xs gt))) $
>   withLayer True True (PatternTop (s ::: sc)) $
>     inferPat (rawCoerce gt) xs $ \ (xs', _, vs, gt' ::: _, ty) -> do
>       unifySolveConstraints
>       solveOrSuspend
>       return $ Alt xs' (renameTypes (renameVS vs) gt') ::: ty


> checkGuardTerms :: Rho -> SGuardTerms () -> Contextual (GuardTerms ())
> checkGuardTerms rho (Unguarded t ds)  = do
>     (ds', bs) <- checkLocalDecls ds
>     withLayer False False (LetBody bs) $ do
>         t' <- checkRho rho t
>         unifySolveConstraints
>         solveConstraints
>         return $ Unguarded t' ds'
> checkGuardTerms rho (Guarded gts ds)  = do
>     (ds', bs) <- checkLocalDecls ds
>     withLayer False False (LetBody bs) $ do
>         Guarded <$> traverse chk gts <*> pure ds'
>   where
>     chk (g :*: t) = withLayer False True GuardTop $ do
>         g' <- checkGuard g
>         checkLocalHypotheses GuardTop
>         t' <- checkRho rho t
>         unifySolveConstraints
>         solveConstraints
>         return $ g' :*: t'


> inferGuardTerms :: SGuardTerms () -> Contextual (GuardTerms () ::: Rho)
> inferGuardTerms (Unguarded e ds) = do
>     (ds', bs) <- checkLocalDecls ds
>     withLayer False False (LetBody bs) $ do
>         e' ::: r <- inferRho e
>         return $ Unguarded e' ds' ::: r
> inferGuardTerms (Guarded gts ds) = do
>     (ds', bs) <- checkLocalDecls ds
>     withLayer False False (LetBody bs) $ do
>         xs <- traverse (\ (g :*: t) -> do
>                           g' <- checkGuard g 
>                           t' ::: r <- inferRho t
>                           return $ (g' :*: t') ::: r) gts
>         let gts' ::: tys = unzipAsc xs
>         ty <- unifyList tys
>         return $ Guarded gts' ds' ::: ty


> checkGuard :: SGuard () -> Contextual (Guard ())
> checkGuard (NumGuard ps)  = NumGuard <$> traverse learnPred ps
>   where
>     learnPred p = do
>       p' <- checkPredKind Pi B0 p
>       modifyContext (:< Constraint Given (predToConstraint p'))
>       return p'
> checkGuard (ExpGuard ts)   = ExpGuard <$> traverse (checkRho tyBool) ts

 


> checkPat :: Bool -> Rho -> SPatternList o a ->
>               (forall b x . (PatternList () b, Ext () b x, VarSuffix () b, Rho) -> Contextual p) ->
>                 Contextual p

> checkPat _ ty P0 q = q (P0, E0, VS0, ty)

> checkPat top ty (PatVar v :! ps) q = do
>     (dom, cod) <- unifyFun ty
>     withLayer False False (LamBody (v ::: dom)) $
>         checkPat top cod ps $ \ (xs, ex, vs, r) ->
>             q (PatVar v :! xs, ex, vs, r)

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
>         checkPat top cod ps $ \ (xs, xex, _, r) ->
>             renameTypes2 (renameVS yvs) xex xs $ \ xex' xs' ->
>                 extComp yex xex' $ \ ex ->
>                     q (PatCon c ys :! xs', ex, error "checkPat vs", r)

> checkPat top ty (PatIgnore :! ps) q = do
>     (_, cod) <- unifyFun ty
>     checkPat top cod ps $ \ (xs, ex, vs, r) ->
>         q (PatIgnore :! xs, ex, vs, r)

> checkPat top ty (PatIntLit i :! ps) q = do
>     (dom, cod) <- unifyFun ty
>     unify dom tyInteger
>     checkPat top cod ps $ \ (xs, ex, vs, r) ->
>         q (PatIntLit i :! xs, ex, vs, r)

> checkPat top ty (PatNPlusK n k :! ps) q = do
>     (dom, cod) <- unifyFun ty
>     unify dom tyInteger
>     withLayer False False (LamBody (n ::: tyInteger)) $ 
>         checkPat top cod ps $ \ (xs, ex, vs, r) ->
>             q (PatNPlusK n k :! xs, ex, vs, r)

> checkPat top (Bind Pi x KNum t) (PatBraceK k :! ps) q = do
>     b        <- fresh SysVar x KNum (Some (TyInt k))
>     aty      <- instS (UserVar All) Given Fixed (unbindTy b t)
>     checkPat top aty ps $ \ (xs, ex, vs, r) -> 
>         q (PatBraceK k :! xs, ex, vs, r)

> checkPat top (Bind Pi _ KNum t) (PatBrace a 0 :! ps) q =
>   withLayer False False (LamBody (a ::: tyInteger)) $ do
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

> checkPat top (Bind Pi x KNum t) (PatBrace a k :! ps) q = 
>   withLayer False False (LamBody (a ::: tyInteger)) $ do
>     b <- freshVar SysVar ("_" ++ x ++ "_" ++ a ++ "_" ++ "oo") KNum
>     let  t'  = unbindTy b t
>          d   = if top || b `elemTarget` t'
>                       then Fixed
>                       else Exists
>     am <- fresh (UserVar Pi) a KNum d
>     modifyContext (:< A (b := Some (TyVar am + TyInt k)))
>     modifyContext (:< Constraint Given (tyPred LE 0 (TyVar am)))
>     aty      <- instS (UserVar All) Given Fixed t'
>     checkPat top aty ps $ \ (xs, ex, vs, r) -> 
>       bindUn am ex vs xs $ \ ex' vs' xs' ->
>         extComp (EC E0) ex' $ \ ex'' ->
>           q (PatBrace a k :! xs', ex'', vs', r)

> checkPat _ ty (p :! _) _ =
>     erk $ "checkPat: couldn't match pattern " ++ renderMe p
>                ++ " against type " ++ renderMe (fogSysTy ty)



> inferPat :: SGuardTerms () -> SPatternList o a ->
>     (forall b x . (PatternList () b, Ext () b x, VarSuffix () b, GuardTerms () ::: Rho, Rho) -> Contextual p) ->
>                 Contextual p

> inferPat t P0 q = do
>     t' ::: r <- inferGuardTerms t
>     q (P0, E0, VS0, t' ::: r, r)

> inferPat top (PatVar v :! ps) q = do
>     a <- unknownTyVar "_a" KSet
>     withLayer False False (LamBody (v ::: a)) $
>         inferPat top ps $ \ (xs, ex, vs, tr, ty) -> 
>             q (PatVar v :! xs, ex, vs, tr, a --> ty)

> inferPat top (PatCon c as :! ps) q = do
>     cty <- inLocation (text "in pattern" <++> prettyHigh (PatCon c as)) $ do
>         sc   <- lookupTmCon c
>         cty  <- existentialise $ instS SysVar Given Hole sc
>         unless (patLength as == args cty) $
>             errConUnderapplied c (args cty) (patLength as)
>         return cty
>     checkPat False cty as $ \ (ys, yex, yvs, s) ->
>       inferPat top ps $ \ (xs, xex, _, tr, ty) ->
>         renameTypes2 (renameVS yvs) xex xs $ \ xex' xs' ->
>           extComp yex xex' $ \ ex ->
>             q (PatCon c ys :! xs', ex, error "inferPat vs", tr, s --> ty)

> inferPat top (PatIgnore :! ps) q = do
>     b <- unknownTyVar "_b" KSet
>     inferPat top ps $ \ (xs, ex, vs, tr, ty) ->
>         q (PatIgnore :! xs, ex, vs, tr, b --> ty)

> inferPat top (PatIntLit i :! ps) q =
>     inferPat top ps $ \ (xs, ex, vs, tr, ty) ->
>         q (PatIntLit i :! xs, ex, vs, tr, tyInteger --> ty)

> inferPat top (PatNPlusK n k :! ps) q = 
>     withLayer False False (LamBody (n ::: tyInteger)) $ 
>         inferPat top ps $ \ (xs, ex, vs, tr, ty) ->
>             q (PatNPlusK n k :! xs, ex, vs, tr, tyInteger --> ty)

> inferPat top (PatBrace a 0 :! ps) q = do
>     n <- fresh (UserVar Pi) a KNum Exists
>     withLayer True True GenMark $ withLayer False False (LamBody (a ::: tyInteger)) $
>       inferPat top ps $ \ (xs, ex, vs, tr, ty) -> do
>         (ty', _) <- generalise ty ([] :: [Alternative ()])
>         bindUn n ex vs xs $ \ ex' vs' xs' ->
>           extComp (EC E0) ex' $ \ ex'' ->
>             q (PatBrace a 0 :! xs', ex'', vs', tr,
>                 Bind Pi a KNum (bindTy n ty'))

> inferPat _ (p :! _) _ =
>     erk $ "inferPat: couldn't infer type of pattern " ++ renderMe p
