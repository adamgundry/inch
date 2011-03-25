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


> subsCheck :: Sigma -> Sigma -> Contextual a ()
> subsCheck s t = do
>     -- mtrace $ "subsCheck:\n    " ++ renderMe s ++ "\n    " ++ renderMe t
>     t  <- specialise t
>     s  <- instantiate s
>     case (s, t) of
>         (TyApp (TyApp (TyB Arr) s1) s2, _) -> do
>             (t1, t2) <- splitFun t
>             subsCheck t1 s1
>             subsCheck s2 t2
>         (_, TyApp (TyApp (TyB Arr) t1) t2) -> do
>             (s1, s2) <- splitFun s
>             subsCheck t1 s1
>             subsCheck s2 t2
>         (Bind b1 a1 k1 t1, Bind b2 a2 k2 t2) | b1 == b2 && k1 == k2 -> do
>             nm <- fresh (a1 ++ "_sc") (Fixed ::: k1)
>             subsCheck (unbind nm t1) (unbind nm t2)
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
>     qs <- solveConstraints True
>     g <- getContext
>     -- mtrace $ "checkSigma: " ++ renderMe g
>     putContext =<< help as g (map Right qs)
>     return t
>   where
>     getNames (_ :< Layer GenMark) = []
>     getNames (g :< A (a := _ ::: _)) = a : getNames g
>     getNames (g :< e) = getNames g

>     help :: [TyName] -> Context -> [Either TyEntry NormalPredicate] ->
>         Contextual () Context
>     help [] (g :< Layer GenMark) h = return $ g <><| h
>     help as (g :< Layer GenMark) h = fail $ "Bad as " ++ show as
>     help as (g :< A (a := Fixed ::: k)) h  | a <? h = fail "Bad h"
>                                            | otherwise = help (delete a as) g h
>     help as (g :< A (a := Some d ::: k)) h = help as g (map (rep k a d) h)
>     help as (g :< A a) h = help as g (Left a : h)
>     help as (g :< Constraint Wanted p) h = help as g (Right p : h) 
>     help as (g :< Constraint Given p) h = help as g h
>     help as B0 h = error "checkSigma help: ran out of context"

>     g <><| h = g <><< map toEnt h
>     toEnt (Left a) = A a
>     toEnt (Right p)  = Constraint Wanted p

>     rep :: Kind -> TyName -> Type -> Either TyEntry NormalPredicate
>                -> Either TyEntry NormalPredicate
>     rep k a t (Left (b := Some d ::: l)) =
>         Left (b := Some (replaceTy k a t d) ::: l)
>     rep k a t (Left e) = Left e
>     rep KindNum a t (Right p) =
>         Right (substNormPred a (normalNum $ toNum t) p)
>     rep k a t (Right p) = Right p

> checkInfer :: Maybe Rho -> STerm -> Contextual () (Term ::: Rho)

> checkInfer mty (TmVar x) = do
>     sc  <- tyOf <$> lookupTmVar x
>     ty  <- instSigma sc mty
>     return $ TmVar x ::: ty

> checkInfer mty (TmCon c) = do
>     sc  <- lookupTmCon c
>     ty  <- instSigma sc mty
>     return $ TmCon c ::: ty

> checkInfer mty (TmInt k) = instSigma (TyB NumTy) mty >>
>                            return (TmInt k ::: TyB NumTy)

> checkInfer mty (TmApp f (TmBrace n)) = do
>     f ::: fty   <- inferRho f   
>     case fty of
>         Bind Pi x KindNum aty -> do
>             n     <- checkNumKind B0 n
>             nm    <- fresh "_n" (Some (TyNum n) ::: KindNum)
>             aty'  <- instantiate (unbind nm aty)
>             traverse (unify aty') mty
>             return $ TmApp f (TmBrace n) ::: aty'
>         _ -> fail $ "Inferred type " ++ renderMe fty ++ " of " ++
>                  renderMe f ++ " is not a pi-type with numeric domain"

> checkInfer mty (TmApp f s) = do
>     f ::: fty   <- inferRho f
>     (dom, cod)  <- splitFun fty
>     s           <- checkSigma dom s
>     instSigma cod mty
>     return $ TmApp f s ::: cod

> checkInfer (Just r) (Lam x t) = do
>     (dom, cod) <- splitFun r
>     b <- withLayer (LamBody (x ::: dom) ()) $ checkRho cod (unbind x t)
>     return $ Lam x (bind x b) ::: r

> checkInfer Nothing (Lam x t) = do
>     a <- unknownTyVar $ x ::: Set
>     b ::: ty <- withLayer (LamBody (x ::: a) ()) $ inferRho (unbind x t)
>     return $ Lam x (bind x b) ::: a --> ty

> checkInfer mty (Let ds t) = do
>     ds <- traverse checkFunDecl ds
>     -- mtrace . ("checkInfer Let:\n" ++) . renderMe =<< getContext
>     t ::: ty <- withLayer (LetBody (map funDeclToBinding ds) ()) $ checkInfer mty t
>     -- mtrace . ("checkInfer Let 2:\n" ++) . renderMe =<< getContext
>     return $ Let ds t ::: ty

> checkInfer mty (t :? xty) = do
>     sc ::: _  <- inferKind B0 xty
>     t         <- checkSigma sc t
>     r         <- instSigma sc mty
>     return $ (t :? sc) ::: r

> checkInfer mty (TmBrace n) = fail "Braces aren't cool"


> funDeclToBinding (FunDecl x (Just ty) _) = x ::: ty

> withLayer :: TermLayer -> Contextual () t -> Contextual () t
> withLayer l m = modifyContext (:< Layer l) *> m <* modifyContext extract
>   where
>     extract (g :< Layer l') | matchLayer l l'  = g
>     extract (g :< e)                           = extract g :< e

>     matchLayer (PatternTop (x ::: _) _ _ _) (PatternTop (y ::: _) _ _ _) = x == y
>     matchLayer FunTop FunTop = True
>     matchLayer (LamBody (x ::: _) ()) (LamBody (y ::: _) ()) = x == y
>     matchLayer (LetBody _ _) (LetBody _ _) = True
>     matchLayer (AnnotLeft _ _) (AnnotLeft _ _) = True
>     matchLayer (AppLeft _ _ _) (AppLeft _ _ _) = True
>     matchLayer (AppRight _ _) (AppRight _ _) = True
>     matchLayer _ _ = False

> inferRho :: STerm -> Contextual () (Term ::: Rho)
> inferRho t = inLocation (text "in inferred expression" <+> prettyHigh t) $
>     checkInfer Nothing t

> checkRho :: Type -> STerm -> Contextual () Term
> checkRho ty t = inLocation (text "in checked expression" <+> prettyHigh t) $
>     tmOf <$> checkInfer (Just ty) t


> splitFun :: Rho -> Contextual a (Sigma, Rho)
> splitFun (TyApp (TyApp (TyB Arr) s) t) = return (s, t)
> splitFun ty = do
>     n <- freshName
>     a <- unknownTyVar $ "_dom" ++ show n ::: Set
>     b <- unknownTyVar $ "_cod" ++ show n ::: Set
>     unify (a --> b) ty
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


> solveConstraints :: Bool -> Contextual t [NormalPredicate]
> solveConstraints try = do
>     g <- getContext
>     let (g', hs, ps) = collect g [] []
>     putContext g'
>     -- mtrace $ "solveConstraints: hs = " ++ show (fsepPretty hs)
>     -- mtrace $ "solveConstraints: ps = " ++ show (fsepPretty ps)
>     qs <- filterM (formulaic hs) ps
>     case (qs, try) of
>       ([],   _      ) -> return []
>       (_:_,  True   ) -> return qs
>       (_:_,  False  ) -> errCannotDeduce hs qs
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
>     collect (g :< Layer GenMark) hs ps = (g :< Layer GenMark, collectHyps g [] ++ hs, ps)
>     -- collect (g :< Layer FunTop) hs ps = (g :< Layer FunTop, collectHyps g [] ++ hs, ps)
>     collect (g :< e) hs ps = collect g hs ps <:< e
>
>     collectHyps B0 hs = hs
>     collectHyps (g :< Constraint Given h) hs = collectHyps g (h:hs)
>     collectHyps (g :< _) hs = collectHyps g hs

>     (g, a, b) <:< e = (g :< e, a, b)


> solveOrSuspend :: Bool -> Contextual t ()
> solveOrSuspend False  = solveConstraints False >> return ()
> solveOrSuspend True   = want =<< solveConstraints True
>   where
>     want :: [NormalPredicate] -> Contextual t ()
>     want [] = return ()
>     want (p:ps) | nonsense p  = fail $ "Impossible constraint " ++ renderMe p
>                 | otherwise   = modifyContext (:< Constraint Wanted p)
>                                 >> want ps
>
>     nonsense :: NormalPredicate -> Bool
>     nonsense (IsZero n) = maybe False (/= 0) (getConstant n)
>     nonsense (IsPos  n) = maybe False (< 0)  (getConstant n)



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


> generalise :: Type -> [Pattern] -> Contextual t (Type, [Pattern])
> generalise t ps = do
>     g <- getContext
>     (g', tps) <- help g (t, ps)
>     putContext g'
>     return tps
>   where
>     help g@(_ :< Layer FunTop)               tps = return (g, tps)
>     -- help g@(_ :< Layer (PatternTop _ _ _)) tps = return (g, tps)
>     help (g :< A (an := d ::: k)) (t, ps) | an <? t || an <? ps = case d of
>         Exists  -> errBadExistential an t ps
>         Some d  -> help g (replaceTy k an d t, map (replace3 k an d) ps)
>         _       -> help g (Bind All (fst an) k (bind an t), ps)
>     help (g :< Layer (LamBody _ _)) tps = help g tps
>     help (g :< A _) tps = help g tps
>     help (g :< Constraint Wanted p)       (t, ps)  = help g (Qual (reifyPred p) t, ps)
>     help (g :< Constraint Given _)        tps      = help g tps
>     help g t = fail $ "generalise: can't help " ++ renderMe g





> checkFunDecl :: SFunDeclaration -> Contextual () FunDeclaration

> checkFunDecl (FunDecl s Nothing pats@(Pat xs _ _ : _)) =
>   inLocation (text $ "in declaration of " ++ s) $ withLayer FunTop $ do
>     sty     <- unknownTyVar $ "_sty" ::: Set
>     pattys  <- traverse (inferAlt True (s ::: sty)) pats
>     let ptms ::: ptys = unzipAsc pattys
>     traverse (unify sty) ptys
>     g <- getContext
>     (ty', ptms') <- generalise sty ptms
>     return $ FunDecl s (Just $ simplifyTy ty') ptms'

> checkFunDecl (FunDecl s (Just st) pats@(Pat xs _ _ : _)) = do
>   inLocation (text $ "in declaration of " ++ s) $ withLayer FunTop $ do
>     sty ::: k <- inLocation (text $ "in type of " ++ s) $ inferKind B0 st
>     unless (k == Set) $ errKindNotSet k     
>     sty' <- specialise sty
>     pattys <- traverse (checkAlt False (s ::: sty) sty') pats
>     let ptms ::: ptys = unzipAsc pattys
>     (ty', ptms') <- generalise (head ptys) ptms
>     g <- getContext
>     -- mtrace $ "Checked " ++ s ++ " with |g| = " ++ show (length (trail g))
>     return $ FunDecl s (Just sty) ptms'

> checkFunDecl (FunDecl s _ []) =
>   inLocation (text $ "in declaration of " ++ s) $ fail $ "No alternative"



> checkAlt :: Bool -> String ::: Sigma -> Rho -> SPattern ->
>     Contextual () (Pattern ::: Type)
> checkAlt try (s ::: sc) sty (Pat xs g t) =
>   inLocation (text ("in alternative " ++ s) <+> prettyHigh (Pat xs g t)) $
>   withLayer (PatternTop (s ::: sc) [] [] []) $ do
>     (xs, rty) <- checkPat True sty xs
>     t  <- checkRho rty t
>     unifySolveConstraints
>     solveOrSuspend try
>     return $ Pat xs Trivial t ::: sty

> inferAlt :: Bool -> String ::: Sigma -> SPattern ->
>     Contextual () (Pattern ::: Type)
> inferAlt try (s ::: sc) (Pat xs g t) =
>   inLocation (text ("in alternative " ++ s) <+> prettyHigh (Pat xs g t)) $
>   withLayer (PatternTop (s ::: sc) [] [] []) $ do
>     (xs, t ::: r, ty) <- inferPat t xs
>     unifySolveConstraints
>     solveOrSuspend try
>     return $ Pat xs Trivial t ::: ty


> unifySolveConstraints :: Contextual t ()
> unifySolveConstraints = do
>     (g, ns) <- runWriter . collectEqualities <$> getContext
>     putContext g
>     traverse (unifyZero F0) ns
>     return ()
>   where
>     collectEqualities :: Context -> Writer [NormalNum] Context
>     collectEqualities B0 = return B0
>     collectEqualities (g :< Layer FunTop) = return $ g :< Layer FunTop
>     --collectEqualities (g :< Layer GenMark) = return $ g :< Layer GenMark
>     collectEqualities (g :< Constraint Wanted (IsZero n)) = tell [n]
>         >> collectEqualities g
>     collectEqualities (g :< e) = (:< e) <$> collectEqualities g


> mapPatWriter w = mapWriterT (\ xcs -> xcs >>= \ (x, cs) -> return (x, ([], cs))) w


> {-
> existentialise :: ContextualWriter ([TmName ::: Type], [NormalPredicate]) t Type
>     -> ContextualWriter ([TmName ::: Type], [NormalPredicate]) t Type
> -}

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

 
 
> checkPat :: Bool -> Rho -> [SPatternTerm] -> Contextual () ([PatternTerm], Rho)

> checkPat top ty [] = return ([], ty)

> checkPat top ty (PatVar v : ps) = do
>     (dom, cod) <- splitFun ty
>     modifyContext (:< Layer (LamBody (v ::: dom) ()))
>     (xs, r) <- checkPat top cod ps
>     return (PatVar v : xs, r)

> checkPat top ty (PatCon c as : ps) =
>   inLocation (text "in pattern" <+> prettyHigh (PatCon c as)) $ do
>     (dom, cod) <- splitFun ty
>     sc   <- lookupTmCon c
>     cty  <- existentialise $ instS True (++ "_pat_inst") Given Hole sc
>     unless (length as == args cty) $
>         errConUnderapplied c (args cty) (length as)
>     (ys, s)  <- checkPat False cty as
>     unify dom s
>     -- aty <- mapPatWriter $ inst True id Fixed aty
>     -- lift $ unify s aty
>     (xs, r) <- checkPat top cod ps
>     return (PatCon c ys : xs, r)

> checkPat top ty (PatIgnore : ps) = do
>     (dom, cod) <- splitFun ty
>     (xs, r) <- checkPat top cod ps
>     return (PatIgnore : xs, r)

> checkPat top (Bind Pi x KindNum t) (PatBrace Nothing k : ps) = do
>     nm <- freshS $ "_" ++ x ++ "aa"
>     let d = if top then Fixed
>                    else if nm <? getTarget (unbind nm t) then Hole
>                                                          else Exists
>     modifyContext (:< A (nm := d ::: KindNum))
>     modifyContext (:< Constraint Given (IsZero (mkVar nm -~ mkConstant k)))
>     aty <- instS True id Given Fixed (unbind nm t)
>     (xs, r) <- checkPat top aty ps
>     return (PatBrace Nothing k : xs, r)

> checkPat top (Bind Pi x KindNum t) (PatBrace (Just a) 0 : ps) = do
>     modifyContext (:< Layer (LamBody (a ::: TyB NumTy) ()))
>     am <- freshS a
>     let d = if top then Fixed
>                    else if am <? getTarget (unbind am t) then Hole
>                                                          else Exists
>     modifyContext (:< A (am := d ::: KindNum))
>     aty <- instS True id Given Fixed (unbind am t)
>     (xs, r) <- checkPat top aty ps
>     return (PatBrace (Just a) 0 : xs, r)

> checkPat top (Bind Pi x KindNum t) (PatBrace (Just a) k : ps) = do
>     nm <- freshS $ "_" ++ x ++ "oo"
>     let (d, d') = if top || nm <? getTarget (unbind nm t)
>                       then (Hole, Fixed)
>                       else (Exists, Exists)
>     modifyContext (:< A (nm := d ::: KindNum))
>     am <- fresh a (d' ::: KindNum)
>     modifyContext (:< Layer (LamBody (a ::: TyB NumTy) ()))
>     modifyContext (:< Constraint Given (IsPos (mkVar am)))
>     modifyContext (:< Constraint Given (IsZero (mkVar nm -~ (mkVar am +~ mkConstant k))))
>     aty <- instS True id Given Fixed (unbind nm t)
>     (xs, r) <- checkPat top aty ps
>     return (PatBrace (Just a) k : xs, r)

> checkPat top ty (p : _) =
>     fail $ "checkPat: couldn't match pattern " ++ renderMe p
>                ++ " against type " ++ renderMe ty


> inferPat :: STerm -> [SPatternTerm] ->
>     Contextual () ([PatternTerm], Term ::: Rho, Rho)

> inferPat t [] = do
>     t ::: r <- inferRho t
>     return ([], t ::: r, r)

> inferPat top (PatVar v : ps) = do
>     a <- unknownTyVar $ "_a" ::: Set
>     modifyContext (:< Layer (LamBody (v ::: a) ()))
>     (xs, tr, ty) <- inferPat top ps
>     return (PatVar v : xs, tr, a --> ty)

> inferPat top (PatCon c as : ps) =
>   inLocation (text "in pattern" <+> prettyHigh (PatCon c as)) $ do
>     sc   <- lookupTmCon c
>     cty  <- existentialise $ instS True (++ "_pat_inst") Given Hole sc
>     unless (length as == args cty) $
>         errConUnderapplied c (args cty) (length as)
>     (ys, s) <- checkPat False cty as
>     (xs, tr, ty)  <- inferPat top ps
>     return (PatCon c ys : xs, tr, s --> ty)

> inferPat top (PatIgnore : ps) = do
>     b <- unknownTyVar $ "_b" ::: Set
>     (xs, tr, ty) <- inferPat top ps
>     return (PatIgnore : xs, tr, b --> ty)

> inferPat top (PatBrace (Just a) 0 : ps) = do
>     n <- fresh a (Hole ::: KindNum)
>     modifyContext (:< Layer (LamBody (a ::: TyB NumTy) ()))
>     (xs, tr, ty) <- inferPat top ps
>     return (PatBrace (Just a) 0 : xs, tr,
>         Bind Pi a KindNum (bind n ty))

> inferPat top (p : _) =
>     fail $ "inferPat: couldn't infer type of pattern " ++ renderMe p




>


> {-

> inferCheckPat top (Bind Pi x KindNum t) (PatBrace Nothing k : ps) = do
>     nm <- freshS $ "_" ++ x ++ "aa"
>     let d = if top || nm <? getTarget (unbind nm t) then Hole else Exists
>     modifyContext (:< A (nm := d ::: KindNum))
>     tell ([], [IsZero (mkVar nm -~ mkConstant k)])
>     aty <- mapPatWriter $ inst True id Fixed (unbind nm t)
>     (pts, ty) <- inferCheckPat top aty ps
>     return ((PatBrace Nothing k ::: TyNum (NumVar nm)) : pts, ty)

> inferCheckPat top (Bind Pi x KindNum t) (PatBrace (Just a) 0 : ps) = do
>     tell ([a ::: TyB NumTy], [])
>     am <- freshS a
>     let d = if top || am <? getTarget (unbind am t) then Hole else Exists
>     modifyContext (:< A (am := d ::: KindNum))
>     aty <- mapPatWriter $ inst True id Fixed (unbind am t)
>     (pts, ty) <- inferCheckPat top aty ps
>     return ((PatBrace (Just a) 0 ::: TyNum (NumVar am)) : pts, ty)

> inferCheckPat top (Bind Pi x KindNum t) (PatBrace (Just a) k : ps) = do
>     nm <- freshS $ "_" ++ x ++ "oo"
>     let (d, d') = if top || nm <? getTarget (unbind nm t)
>                       then (Hole, Fixed)
>                       else (Exists, Exists)
>     modifyContext (:< A (nm := d ::: KindNum))
>     am <- fresh a (d' ::: KindNum)
>     tell ([a ::: TyB NumTy], [IsPos (mkVar am), IsZero (mkVar nm -~ (mkVar am +~ mkConstant k))])
>     aty <- mapPatWriter $ inst True id Fixed (unbind nm t)
>     (pts, ty) <- inferCheckPat top aty ps
>     return ((PatBrace (Just a) k ::: TyNum (NumVar nm)) : pts, ty)

> -}



