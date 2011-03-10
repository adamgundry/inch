> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts, PatternGuards #-}

> module TypeCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Maybe
> import Data.Traversable
> import Text.PrettyPrint.HughesPJ

> import qualified Data.Integer.Presburger as P

> import BwdFwd
> import TyNum
> import Type
> import Num
> import Syntax
> import Context
> import Unify
> import Orphans
> import Kit
> import Error
> import PrettyPrinter
> import PrettyContext
> import KindCheck


> {-

If the current term is a lambda, |goLam ty| enters its body, assigning
the type |ty| to the bound variable.

> goLam :: Contextual (Term, Maybe Type) ()
> goLam = do
>     (Lam x t, mty)  <- getT
>     (dom, cod)      <- case mty of
>         Just ty  -> splitFun ty
>         Nothing  -> (,) <$> unknownTyVar ("_dom" ::: Set) <*> unknownTyVar ("_cod" ::: Set)
>     putT (unbind x t, Just cod)
>     modifyContext (:< Layer (LamBody (x ::: dom) ()))


If the current term is an application, |goAppLeft| enters the
function.

> goAppLeft :: Contextual (Term, Maybe Type) ()
> goAppLeft = do
>     (TmApp f s, mty)  <- getT
>     putT (f, Nothing)
>     modifyContext (:< Layer (AppLeft () s mty))


If the current term is an annotation, |goAnnotLeft| enters the term
being annotated.

> goAnnotLeft :: Contextual (Term, Maybe Type) ()
> goAnnotLeft = do
>     (t :? uty, mty) <- getT
>     aty <- case mty of
>         Just ty  -> subsCheck ty uty
>         Nothing  -> instantiate uty
>     putT (t, Just aty)
>     modifyContext (:< Layer (AnnotLeft () uty))


The function |goUp tau _Xi| is called when the term at the current
location has been given type |tau|, and it proceeds up and then right
to find the next type inference problem.

The accumulator |_Xi| collects variable definitions that |tau| may
depend on, and hence must be reinserted into the context once the new
location is found.


> goUp :: [Entry] -> Contextual () Type
> goUp _Xi = do
>     st@(St{tValue = (t, Just ty)}) <- get
>     case context st of
>       (es :< Layer l) ->
>         case l of      
>             AppLeft () (TmBrace n) mty -> do
>                 case ty of
>                     Bind Pi x KindNum aty -> do
>                         putContext (es <><< _Xi)
>                         nm <- fresh "_n" (Some (TyNum n) ::: KindNum)
>                         aty' <- instantiate (unbind nm aty)
>                         case mty of
>                             Just ty  -> unify ty aty'
>                             Nothing  -> return ()
>                         putT (TmApp t (TmBrace n), Just aty')
>                         goUp []
>                     _ -> fail $ "Bad dependent application: type "
>                              ++ render ty ++ " of " ++ render t
>                              ++ " is not good"
>             AppLeft () a mty -> do
>                 putContext (es <><< _Xi)
>                 (dom, cod) <- splitFun ty
>                 case mty of
>                     Just ty  -> unify ty cod
>                     Nothing  -> return ()
>                 modifyContext (:< Layer (AppRight (t ::: dom --> cod) ()))
>                 putT (a, Just dom)
>                 inferType
>             AppRight (f ::: sigma) () -> do
>                 putContext (es <><< _Xi)
>                 (dom, cod) <- splitFun sigma
>                 putT (TmApp f t, Just cod)
>                 goUp []
>             LamBody (x ::: sigma) () -> do
>                 put st{tValue = (Lam x (bind x t), Just (sigma --> ty)),
>                        context = es}
>                 goUp _Xi
>             AnnotLeft () uty -> do
>                 put st{tValue = (t :? uty, Just ty),
>                        context = es}
>                 goUp _Xi
>             PatternTop _ _ _ _ -> do
>                 put st{context = context st <><< _Xi}
>                 return ty
>       (es :< e) -> do
>           put st{context = es}
>           goUp (e : _Xi)
>       B0 -> error (  "Ran out of context when going up from " 
>                      ++ (show t) ++ " : " ++ (show ty))
> -}


> subsCheck :: Type -> Type -> Contextual a Type
> subsCheck s t = do
>     t  <- specialise t
>     s  <- instantiate s
>     unify s t
>     return t


> checkInfer :: Maybe Type -> STerm -> Contextual () (Term ::: Type)

> checkInfer mty (TmVar x) = do
>     sc  <- tyOf <$> lookupTmVar x
>     ty  <- case mty of
>         Just ity  -> subsCheck sc ity
>         Nothing   -> instantiate sc
>     return $ TmVar x ::: ty

> checkInfer mty (TmCon c) = do
>     sc  <- lookupTmCon c
>     ty  <- case mty of
>         Just ity  -> subsCheck sc ity
>         Nothing   -> instantiate sc
>     return $ TmCon c ::: ty

> checkInfer (Just ty)  (TmInt k) = unify ty (TyB NumTy) >> return (TmInt k ::: TyB NumTy)
> checkInfer Nothing    (TmInt k) = return $ TmInt k ::: TyB NumTy

> checkInfer mty (TmApp f (TmBrace n)) = do
>     f ::: Bind Pi x KindNum aty   <- infer f   
>     n     <- checkNumKind B0 n
>     nm    <- fresh "_n" (Some (TyNum n) ::: KindNum)
>     aty'  <- instantiate (unbind nm aty)
>     traverse (unify aty') mty
>     return $ TmApp f (TmBrace n) ::: aty'

> checkInfer mty (TmApp f s) = do
>     f ::: fty   <- infer f
>     (dom, cod)  <- splitFun fty
>     s           <- check dom s
>     traverse (unify cod) mty
>     return $ TmApp f s ::: cod

> checkInfer mty (Lam x t) = do
>     (dom, cod) <- case mty of
>         Just ty  -> splitFun ty
>         Nothing  -> (,) <$> unknownTyVar ("_dom" ::: Set) <*> unknownTyVar ("_cod" ::: Set)
>     b <- withLayer (LamBody (x ::: dom) ()) $ check cod (unbind x t)
>     return $ Lam x (bind x b) ::: dom --> cod

> checkInfer mty (Let ds t) = do
>     ds <- traverse checkFunDecl ds
>     t ::: ty <- withLayer (LetBody (map funDeclToBinding ds) ()) $ do
>         g <- getContext
>         -- mtrace $ "checkInfer Let: " ++ render g
>         checkInfer mty t
>     return $ Let ds t ::: ty

> checkInfer mty (t :? xty) = do
>     uty ::: _ <- inferKind B0 xty
>     aty <- case mty of
>         Just ty  -> subsCheck ty uty
>         Nothing  -> instantiate uty
>     t <- check aty t
>     return $ (t :? uty) ::: aty

> checkInfer mty (TmBrace n) = fail "Braces aren't cool"


> funDeclToBinding (FunDecl x (Just ty) _) = x ::: ty

> withLayer :: TermLayer -> Contextual () t -> Contextual () t
> withLayer l m = modifyContext (:< Layer l) *> m <* modifyContext extract
>   where
>     extract (g :< Layer _)  = g
>     extract (g :< e)        = extract g :< e

> infer :: STerm -> Contextual () (Term ::: Type)
> infer t = inLocation (text "in expression" <+> prettyHigh t) $ checkInfer Nothing t

> check :: Type -> STerm -> Contextual () Term
> check ty t = inLocation (text "in expression" <+> prettyHigh t) $ tmOf <$> checkInfer (Just ty) t


> splitFun :: Type -> Contextual a (Type, Type)
> splitFun (TyApp (TyApp (TyB Arr) s) t) = return (s, t)
> {-
> splitFun (Qual q t) = do
>     q' <- normalisePred q
>     modifyContext (:< Constraint Given q')
>     splitFun t
> -}
> splitFun t = do
>     a <- unknownTyVar $ "_dom" ::: Set
>     b <- unknownTyVar $ "_cod" ::: Set
>     unify (a --> b) t
>     return (a, b)




> inst :: Bool -> (String -> String) -> TypeDef -> Type -> ContextualWriter [NormalPredicate] t Type
> inst pi s d (TyApp f a)     = TyApp f <$> inst pi s d a
> inst True s d (Bind Pi x k t) = return $ Bind Pi x k t
> inst pi s d (Bind b x k t)  = do
>     beta <- fresh (s x) (d ::: k)
>     inst pi s d (unbind beta t)
> inst pi s d (Qual p t)      = do
>     p' <- lift $ normalisePred p
>     tell [p']
>     inst pi s d t
> inst pi s d t               = return t


> instS :: Bool -> (String -> String) -> CStatus -> TypeDef -> Type -> Contextual t Type
> instS pi f s d t = do
>     (ty, cs) <- runWriterT $ inst pi f d t
>     modifyContext (<><< map (Constraint s) cs)
>     return ty


> specialise :: Type -> Contextual t Type
> specialise = instS True id Given Fixed

> instantiate :: Type -> Contextual t Type
> instantiate = instS True (++ "_inst") Wanted Hole


> solveConstraints :: Bool -> Contextual t ()
> solveConstraints try = do
>     g <- getContext
>     let (g', hs, ps) = collect g [] []
>     putContext g'
>     -- mtrace $ "solveConstraints: hs = " ++ show (fsepPretty hs)
>     -- mtrace $ "solveConstraints: ps = " ++ show (fsepPretty ps)
>     qs <- filterM (formulaic hs) ps
>     case (qs, try) of
>       ([],   _      ) -> return ()
>       (_:_,  True   ) -> want qs
>       (_:_,  False  ) -> fail $ "Could not deduce\n    [" ++ show (fsepPretty qs)
>                              ++ "]\nfrom\n    [" ++ show (fsepPretty hs) ++ "]"
>   where
>     formulaic hs p = (not . P.check) <$> toFormula hs p
>
>     collect :: Context -> [NormalPredicate] -> [NormalPredicate] ->
>         (Context, [NormalPredicate], [NormalPredicate])
>     collect B0 hs ps = (B0, hs, ps)
>     collect (g :< Constraint Wanted p)  hs ps = collect g hs (p:ps)
>     collect (g :< Constraint Given h)   hs ps = collect g (h:hs) ps <:< Constraint Given h
>     collect (g :< A e@(a := Some d ::: KindNum)) hs ps =
>         let dn = normalNum (toNum d) in 
>         collect g (subsPreds a dn hs) (subsPreds a dn ps )
>             <:< A e
>     collect (g :< l@(Layer (PatternTop _ _ ks ws))) hs ps = 
>         collect g (ks ++ hs) (ws ++ ps) <:< l
>     collect (g :< e) hs ps = collect g hs ps <:< e
>
>     (g, a, b) <:< e = (g :< e, a, b)
>
>     want :: [NormalPredicate] -> Contextual t ()
>     want [] = return ()
>     want (p:ps) | nonsense p  = fail $ "Impossible constraint " ++ renderMe p
>                 | otherwise   = modifyContext (:< Constraint Wanted p)
>                                 >> want ps
>
>     nonsense :: NormalPredicate -> Bool
>     nonsense (IsZero n) = maybe False (/= 0) (getConstant n)
>     nonsense (IsPos  n) = maybe False (< 0)  (getConstant n)



> {-
> solveConstraints :: Bool -> Contextual t ()
> solveConstraints try = do
>   g <- getContext
>   -- mtrace $ "solveConstraints: " ++ render (expandContext g)
>   seekTruth [] []
>  where
>   seekTruth :: [NormalPredicate] -> [NormalPredicate] -> Contextual t ()
>   seekTruth hs ps = do
>     g <- getContext
>     case g of
>       B0         -> do
>           cs <- catMaybes <$> traverse (deduce hs) ps
>           unless (null cs) $ fail $ "solveConstraints: out of scope error: "
>                                       ++ show (fsepPretty cs)
>       (g :< xD)  -> putContext g >> case xD of
>           Constraint Given h   -> seekTruth (h:hs) ps >> modifyContext (:< xD)
>           Constraint Wanted p  -> seekTruth hs (p:ps)
>           A (a := Some d ::: KindNum) -> do
>               dn <- typeToNum d
>               seekTruth (subsPreds a dn hs) (subsPreds a dn ps)
>               modifyContext (:< xD)
>           A (a := d ::: KindNum) -> case findRewrite a hs of
>               Just n   -> do
>                   seekTruth (subsPreds a n hs) (subsPreds a n ps)
>                   modifyContext (:< xD)
>               Nothing  -> do
>                   let (aps, qs) = partition (a <?) ps
>                   seekTruth (filter (not . (a <?)) hs) qs
>                   modifyContext (:< xD)
>                   -- mtrace $ "hs: " ++ show hs
>                   --          ++ "\na: " ++ show (prettyVar a)
>                   --          ++ "\naps: " ++ show (fsepPretty aps)
>                   --          ++ "\nqs: " ++ show (fsepPretty qs)
>                   cs <- catMaybes <$> traverse (deduce hs) aps
>                   modifyContext (<><< map (Constraint Wanted) cs)
>           Layer (PatternTop _ _ ks ws) -> seekTruth (ks ++ hs) (ws ++ ps)
>           _ -> seekTruth hs ps >> modifyContext (:< xD)

>   deduce :: [NormalPredicate] -> NormalPredicate -> Contextual t (Maybe NormalPredicate)
>   deduce hs (IsZero n)  | isZero n                 = return Nothing
>   deduce hs (IsPos n)   | Just k <- getConstant n  = 
>         if k >= 0  then  return Nothing
>                    else  fail $ "Impossible constraint 0 <= " ++ show k
>   deduce hs p = do
>       f <- toFormula hs p
>       if P.check f
>           then return Nothing
>           else if try
>                then return $ Just p
>                else do
>         g <- getContext
>         fail $ "Could not deduce " ++ render p
>                    ++ " from [" ++ show (fsepPretty hs) ++ "]"
>                    -- ++ " in context\n" ++ render g

> -}

> toFormula :: [NormalPredicate] -> NormalPredicate -> Contextual t P.Formula
> toFormula hs p = do
>     g <- getContext
>     let hs'  = map (expandPred g . reifyPred) hs
>         p'   = expandPred g (reifyPred p)
>     return $ convert (expandContext g) [] hs' p'
>   where
>     convert :: Context -> [(TyName, P.Term)] -> [Predicate] -> Predicate -> P.Formula
>     convert B0 axs hs p =
>         foldr (P.:/\:) P.TRUE (map (predToFormula . apply axs) hs)
>             P.:=>: predToFormula (apply axs p)
>     convert (g :< A (a := _ ::: KindNum)) axs hs p = 
>         P.Forall (\ x -> convert g ((a, x) : axs) hs p)
>     convert (g :< _) axs hs p = convert g axs hs p

>     apply :: [(TyName, P.Term)] -> Predicate -> Pred P.Term
>     apply xs = bindPred (NumVar . fromJust . flip lookup xs)
>                
>     predToFormula :: Pred P.Term -> P.Formula
>     predToFormula (m :==: n)  = numToTerm m P.:=: numToTerm n
>     predToFormula (m :<=: n)  = numToTerm m P.:<=: numToTerm n

>     numToTerm :: TyNum P.Term -> P.Term
>     numToTerm (NumConst k)  = fromInteger k
>     numToTerm (NumVar t)    = t
>     numToTerm (n :+: m)     = numToTerm n + numToTerm m
>     numToTerm (n :*: m)     = numToTerm n * numToTerm m
>     numToTerm (Neg n)       = - numToTerm n


> generalise :: Type -> Contextual t Type
> generalise t = do
>     g <- getContext
>     (g', t') <- help g t
>     putContext g'
>     return t'
>   where
>     help g@(_ :< Layer FunTop)            t = return (g, t)
>     help g@(_ :< Layer (PatternTop _ _ _ _)) t = return (g, t)
>     help (g :< A (an := d ::: k)) t | an <? t = case d of
>         Exists  -> fail $ "Illegal existential " ++ show (prettyVar an) ++
>                           "\nwhen generalising type " ++ renderMe t
>         Some d  -> help g (replaceTy k an d t)
>         _       -> help g (Bind All (fst an) k (bind an t))
>     help (g :< A _) t = help g t
>     help (g :< Constraint Wanted p)       t = help g (Qual (reifyPred p) t)
>     help (g :< Constraint Given _)        t = help g t
>     help g t = fail $ "ERROR: Can't help " ++ renderMe g





> checkFunDecl :: SFunDeclaration -> Contextual () FunDeclaration

> checkFunDecl (FunDecl s Nothing pats@(Pat xs _ _ : _)) =
>   inLocation (text $ "in declaration of " ++ s) $ withLayer FunTop $ do
>     sty     <- unknownTyVar $ "_sty" ::: Set
>     pattys  <- traverse (checkPat True (s ::: sty) sty) pats
>     ty'     <- simplifyTy <$> generalise sty
>     return $ FunDecl s (Just ty') (map tmOf pattys)

> checkFunDecl (FunDecl s (Just st) pats@(Pat xs _ _ : _)) = 
>   inLocation (text $ "in declaration of " ++ s) $ withLayer FunTop $ do
>     sty ::: k <- inLocation (text "in type" <+> prettyHigh st) $ inferKind B0 st
>     unless (k == Set) $ errKindNotSet k
>     sty'  <- instS True id Given Fixed sty
>     pattys <- traverse (checkPat False (s ::: sty) sty') pats
>     let ty = tyOf (head pattys)
>     ty' <- simplifyTy <$> generalise ty 
>     return (FunDecl s (Just sty) (map tmOf pattys))

> checkFunDecl (FunDecl s _ []) =
>   inLocation (text $ "in declaration of " ++ s) $ fail $ "No alternative"



> checkPat :: Bool -> String ::: Type -> Type -> SPattern -> Contextual () (Pattern ::: Type)
> checkPat try (s ::: sc) sty (Pat xs g t) =
>   inLocation (text ("in alternative " ++ s) <+> prettyHigh (Pat xs g t)) $ do
>    ((xs', rty), (bs, ps)) <- runWriterT $ checkPatTerms True sty xs
>    rty <- specialise rty
>    withLayer (PatternTop (s ::: sc) bs ps []) $ do
>     t'  <- check rty t
>     let  xtms ::: xtys  = unzipAsc xs'
>          ty             = xtys /-> rty

>     -- mtrace . (s ++) . (" checkPat context: " ++) . renderMe . expandContext =<< getContext
>     unifySolveConstraints
>     solveConstraints try
>
>     -- mtrace . (s ++) . (" checkPat context: " ++) . show . prettyHigh =<< getContext
>     -- mtrace . (s ++) . (" checkPat ty: " ++) . renderMe =<< niceType ty
>     return $ Pat xtms Trivial t' ::: ty

> unifySolveConstraints :: Contextual t ()
> unifySolveConstraints = do
>     ns <- collectEqualities <$> getContext
>     traverse (unifyZero F0) ns
>     return ()
>   where
>     collectEqualities :: Context -> [NormalNum]
>     collectEqualities B0 = []
>     collectEqualities (g :< Constraint Wanted (IsZero n)) = n : collectEqualities g
>     collectEqualities (g :< _) = collectEqualities g


> mapPatWriter w = mapWriterT (\ xcs -> xcs >>= \ (x, cs) -> return (x, ([], cs))) w


> existentialise :: ContextualWriter ([TmName ::: Type], [NormalPredicate]) t Type
>     -> ContextualWriter ([TmName ::: Type], [NormalPredicate]) t Type
> existentialise m = do
>     modifyContext (:< Layer FunTop) -- hackish
>     ty <- m
>     modifyContext $ help (getTarget ty)
>     return ty
>   where
>     help ty (g :< Layer FunTop)                      = g
>     help ty (g :< A (a := Hole ::: k))  | a <? ty    = help ty g :< A (a := Hole ::: k)
>                                         | otherwise  = help ty g :< A (a := Exists ::: k)
>     help ty (g :< e)                                 = help ty g :< e

> checkPatTerms :: Bool -> Type -> [SPatternTerm] ->
>     ContextualWriter ([TmName ::: Type], [NormalPredicate]) ()
>     ([PatternTerm ::: Type], Type)
>
> checkPatTerms top t [] = return ([], t)
>
> checkPatTerms top sat (PatVar v : ps) = do
>     sat <- mapPatWriter $ inst True id Fixed sat
>     (s, t) <- lift $ splitFun sat
>     tell ([v ::: s], [])
>     (pts, ty) <- checkPatTerms top t ps
>     return ((PatVar v ::: s) : pts, ty)
>
> checkPatTerms top sat (PatCon c xs : ps) =
>   inLocation (text "in pattern" <+> prettyHigh (PatCon c xs)) $ do
>     sat <- mapPatWriter $ inst True id Fixed sat
>     (s, t) <- lift $ splitFun sat
>     sc   <- lookupTmCon c
>     cty  <- existentialise $ mapPatWriter $ inst True (++ "_pat_inst") Hole sc
>     unless (length xs == args cty) $
>         errConUnderapplied c (args cty) (length xs)
>     (pts, aty)  <- checkPatTerms False cty xs
>     aty <- mapPatWriter $ inst True id Fixed aty
>     lift $ unify s aty
>     (pps, ty) <- checkPatTerms top t ps
>     return ((PatCon c (map tmOf pts) ::: s) : pps, ty)
>  
> checkPatTerms top sat (PatIgnore : ps) = do
>     (s, t) <- lift $ splitFun sat
>     (pts, ty) <- checkPatTerms top t ps
>     return ((PatIgnore ::: s) : pts, ty)
>
> checkPatTerms top (Bind Pi x KindNum t) (PatBrace Nothing k : ps) = do
>     nm <- freshS $ "_" ++ x ++ "aa"
>     let d = if top || nm <? getTarget (unbind nm t) then Hole else Exists
>     modifyContext (:< A (nm := d ::: KindNum))
>     tell ([], [IsZero (mkVar nm -~ mkConstant k)])
>     aty <- mapPatWriter $ inst True id Fixed (unbind nm t)
>     (pts, ty) <- checkPatTerms top aty ps
>     return ((PatBrace Nothing k ::: TyNum (NumVar nm)) : pts, ty)

> checkPatTerms top (Bind Pi x KindNum t) (PatBrace (Just a) 0 : ps) = do
>     tell ([a ::: TyB NumTy], [])
>     am <- freshS a
>     let d = if top || am <? getTarget (unbind am t) then Hole else Exists
>     modifyContext (:< A (am := d ::: KindNum))
>     aty <- mapPatWriter $ inst True id Fixed (unbind am t)
>     (pts, ty) <- checkPatTerms top aty ps
>     return ((PatBrace (Just a) 0 ::: TyNum (NumVar am)) : pts, ty)

> checkPatTerms top (Bind Pi x KindNum t) (PatBrace (Just a) k : ps) = do
>     nm <- freshS $ "_" ++ x ++ "oo"
>     let (d, d') = if top || nm <? getTarget (unbind nm t)
>                       then (Hole, Fixed)
>                       else (Exists, Exists)
>     modifyContext (:< A (nm := d ::: KindNum))
>     am <- fresh a (d' ::: KindNum)
>     tell ([a ::: TyB NumTy], [IsPos (mkVar am), IsZero (mkVar nm -~ (mkVar am +~ mkConstant k))])
>     aty <- mapPatWriter $ inst True id Fixed (unbind nm t)
>     (pts, ty) <- checkPatTerms top aty ps
>     return ((PatBrace (Just a) k ::: TyNum (NumVar nm)) : pts, ty)

> checkPatTerms top ty (p : _) = fail $ "checkPatTerms: couldn't match pattern "
>                            ++ renderMe p ++ " against type " ++ renderMe ty