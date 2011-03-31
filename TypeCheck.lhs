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

> inst :: (String -> String) -> TypeDef -> Type ->
>             ContextualWriter [NormalPredicate] t Type
> inst s d (TyApp (TyApp (TyB Arr) a) t) =
>     TyApp (TyApp (TyB Arr) a) <$> inst s d t
> inst s d (Bind All x k t) = do
>     beta <- fresh (s x) (d ::: k)
>     inst s d (unbind beta t)
> inst s d (Qual p t) = do
>     p' <- lift $ normalisePred p
>     tell [p']
>     inst s d t
> inst s d t = return t


The |instS| function is like |inst|, but also takes a constraint
status, and stores the predicates in the context with the given
status.

> instS :: (String -> String) -> CStatus -> TypeDef -> Type ->
>              Contextual t Type
> instS f s d t = do
>     (ty, cs) <- runWriterT $ inst f d t
>     modifyContext (<><< map (Constraint s) cs)
>     return ty

> specialise :: Type -> Contextual t Type
> specialise = instS id Given Fixed

> instantiate :: Type -> Contextual t Type
> instantiate = instS (++ "_inst") Wanted Hole


> existentialise :: (MonadState (ZipState t) m, FV a) =>
>                       m (Ty k a) -> m (Ty k a)
> existentialise m = do
>     modifyContext (:< Layer FunTop) -- hackish
>     ty <- m
>     modifyContext $ help (getTarget ty)
>     return ty
>   where
>     help ty (g :< A (a := Hole ::: k))
>         | a <? ty                = help ty g :< A (a := Hole ::: k)
>         | otherwise              = help ty g :< A (a := Exists ::: k)
>     help ty (g :< Layer FunTop)  = g
>     help ty (g :< e)             = help ty g :< e


> generalise :: Type -> [Pattern] -> Contextual t (Type, [Pattern])
> generalise t ps = do
>     g <- getContext
>     (g', tps) <- help g (t, ps)
>     putContext g'
>     return tps
>   where
>     help g@(_ :< Layer FunTop)                tps = return (g, tps)
>     help g@(_ :< Layer (PatternTop _ _ _ _))  tps = return (g, tps)
>     help (g :< A (an := d ::: k)) (t, ps)
>       | an <? t || an <? ps = case d of
>         Exists  -> errBadExistential an t ps
>         Some d  -> help g (replaceTy k an d t, map (replace3 k an d) ps)
>         _       -> help g (Bind All (fst an) k (bind an t), ps)
>     help (g :< Layer (LamBody _ _))  tps      = help g tps
>     help (g :< A _)                  tps      = help g tps
>     help (g :< Constraint Given _)   tps      = help g tps
>     help (g :< Constraint Wanted p)  (t, ps)  =
>         help g (Qual (reifyPred p) t, ps)
>     help g tps = erk $ "generalise: can't help " ++ renderMe g




> layerStops :: TermLayer -> Maybe (TermLayer, [NormalPredicate], [NormalPredicate])
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
>     collect (g :< A e@(a := Some d ::: KindNum)) hs ps =
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
>         | nonsense p  = erk $ "Impossible constraint " ++ renderMe p
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
>     convert :: Context -> [(TyName, P.Term)] -> [Predicate] ->
>                    Predicate -> P.Formula
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





> subsCheck :: Sigma -> Sigma -> Contextual a ()
> subsCheck s t = do
>     t  <- specialise t
>     s  <- instantiate s
>     case (s, t) of
>         (TyApp (TyApp (TyB Arr) s1) s2, _) -> do
>             (t1, t2) <- unifyFun t
>             subsCheck t1 s1
>             subsCheck s2 t2
>         (_, TyApp (TyApp (TyB Arr) t1) t2) -> do
>             (s1, s2) <- unifyFun s
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
>     solveOrSuspend
>     g <- getContext
>     putContext =<< help as g []
>     return t
>   where
>     getNames (_ :< Layer GenMark) = []
>     getNames (g :< A (a := _ ::: _)) = a : getNames g
>     getNames (g :< e) = getNames g

>     help :: [TyName] -> Context -> [Either TyEntry NormalPredicate] ->
>                 Contextual () Context
>     help [] (g :< Layer GenMark) h  = return $ g <><| h
>     help as (g :< Layer GenMark) h  = erk $ "Bad as: " ++ show as
>     help as (g :< A (a := Fixed ::: k)) h
>         | a <? h     = erk "checkSigma help: bad h"
>         | otherwise  = help (delete a as) g h
>     help as (g :< A (a := Some d ::: k)) h = help as g (map (rep k a d) h)
>     help as (g :< A a) h                   = help as g (Left a : h)
>     help as (g :< Constraint Wanted p) h   = help as g (Right p : h) 
>     help as (g :< Constraint Given p) h    = help as g h
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

> checkInfer mty (TmInt k) = do
>     instSigma (TyB NumTy) mty
>     return (TmInt k ::: TyB NumTy)

> checkInfer mty (TmApp f (TmBrace n)) = do
>     f ::: fty  <- inferRho f   
>     case fty of
>         Bind Pi x KindNum aty -> do
>             n   <- checkNumKind B0 n
>             nm  <- fresh "_n" (Some (TyNum n) ::: KindNum)
>             ty  <- instSigma (unbind nm aty) mty
>             return $ TmApp f (TmBrace n) ::: ty
>         _ -> erk $ "Inferred type " ++ renderMe fty ++ " of " ++
>                  renderMe f ++ " is not a pi-type with numeric domain"

> checkInfer mty (TmApp f s) = do
>     f ::: fty   <- inferRho f
>     (dom, cod)  <- unifyFun fty
>     s           <- checkSigma dom s
>     instSigma cod mty
>     return $ TmApp f s ::: cod

> checkInfer (Just r) (Lam x t) = do
>     (dom, cod) <- unifyFun r
>     b <- withLayer (LamBody (x ::: dom) ()) $ checkRho cod (unbind x t)
>     return $ Lam x (bind x b) ::: r

> checkInfer Nothing (Lam x t) = do
>     a <- unknownTyVar $ x ::: Set
>     b ::: ty <- withLayer (LamBody (x ::: a) ()) $ inferRho (unbind x t)
>     return $ Lam x (bind x b) ::: a --> ty

> checkInfer mty (Let ds t) = do
>     ds <- traverse checkFunDecl ds
>     t ::: ty <- withLayer (LetBody (map funDeclToBinding ds) ()) $
>                     checkInfer mty t
>     return $ Let ds t ::: ty

> checkInfer mty (t :? xty) = do
>     sc ::: _  <- inferKind B0 xty
>     t         <- checkSigma sc t
>     r         <- instSigma sc mty
>     return $ (t :? sc) ::: r

> checkInfer mty (TmBrace n) = erk "Braces aren't cool"


> funDeclToBinding (FunDecl x (Just ty) _) = x ::: ty

> withLayer :: TermLayer -> Contextual () t -> Contextual () t
> withLayer l m = modifyContext (:< Layer l) *> m <* modifyContext extract
>   where
>     extract (g :< Layer l') | matchLayer l l'  = g
>     extract (g :< e)                           = extract g :< e

>     matchLayer (PatternTop (x ::: _) _ _ _)
>                (PatternTop (y ::: _) _ _ _) = x == y
>     matchLayer FunTop FunTop = True
>     matchLayer (LamBody (x ::: _) ()) (LamBody (y ::: _) ()) = x == y
>     matchLayer (LetBody _ _) (LetBody _ _) = True
>     matchLayer (AnnotLeft _ _) (AnnotLeft _ _) = True
>     matchLayer (AppLeft _ _ _) (AppLeft _ _ _) = True
>     matchLayer (AppRight _ _) (AppRight _ _) = True
>     matchLayer _ _ = False

> inferRho :: STerm -> Contextual () (Term ::: Rho)
> inferRho t =
>   inLocation (text "in inferred expression" <+> prettyHigh t) $
>     checkInfer Nothing t

> checkRho :: Type -> STerm -> Contextual () Term
> checkRho ty t =
>   inLocation (text "in checked expression" <+> prettyHigh t) $
>     tmOf <$> checkInfer (Just ty) t



> checkFunDecl :: SFunDeclaration -> Contextual () FunDeclaration

> checkFunDecl (FunDecl s Nothing pats@(Pat xs _ _ : _)) =
>   inLocation (text $ "in declaration of " ++ s) $ withLayer FunTop $ do
>     sty     <- unknownTyVar $ "_sty" ::: Set
>     pattys  <- traverse (inferAlt (s ::: sty)) pats
>     let ptms ::: ptys = unzipAsc pattys
>     traverse (unify sty) ptys
>     g <- getContext
>     (ty', ptms') <- generalise sty ptms
>     return $ FunDecl s (Just $ simplifyTy ty') ptms'

> checkFunDecl (FunDecl s (Just st) pats@(Pat xs _ _ : _)) = do
>   inLocation (text $ "in declaration of " ++ s) $ withLayer FunTop $ do
>     sty ::: k <- inLocation (text $ "in type of " ++ s) $ inferKind B0 st
>     unless (k == Set) $ errKindNotSet k     
>     ptms <- traverse (checkAlt (s ::: sty)) pats
>     return $ FunDecl s (Just sty) ptms

> checkFunDecl (FunDecl s _ []) =
>   inLocation (text $ "in declaration of " ++ s) $ erk $ "No alternative"



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
>     (_, [p]) <- generalise (TyB Arr) [Pat xs g t] -- to fix up variables
>     return p

> inferAlt :: String ::: Sigma -> SPattern ->
>                 Contextual () (Pattern ::: Type)
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
> checkGuard (ExpGuard t)   = ExpGuard <$> checkRho (TyCon "Bool") t

 
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
>     cty  <- existentialise $ instS (++ "_pat_inst") Given Hole sc
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

> checkPat top (Bind Pi x KindNum t) (PatBrace Nothing k : ps) = do
>     nm       <- fresh ("_" ++ x ++ "aa") (Some (TyNum (NumConst k)) ::: KindNum)
>     aty      <- instS id Given Fixed (unbind nm t)
>     (xs, r)  <- checkPat top aty ps
>     return (PatBrace Nothing k : xs, r)

> checkPat top (Bind Pi x KindNum t) (PatBrace (Just a) 0 : ps) = do
>     modifyContext (:< Layer (LamBody (a ::: TyB NumTy) ()))
>     nm <- freshS a
>     let  t'  = unbind nm t
>          d   = if top || nm <? getTarget t'
>                    then Fixed
>                    else Exists
>     modifyContext (:< A (nm := d ::: KindNum))
>     aty      <- instS id Given Fixed t'
>     (xs, r)  <- checkPat top aty ps
>     return (PatBrace (Just a) 0 : xs, r)

> checkPat top (Bind Pi x KindNum t) (PatBrace (Just a) k : ps) = do
>     modifyContext (:< Layer (LamBody (a ::: TyB NumTy) ()))
>     nm <- freshS $ "_" ++ x ++ "_" ++ a ++ "_" ++ "oo"
>     let  t'  = unbind nm t
>          d   = if top || nm <? getTarget t'
>                       then Fixed
>                       else Exists
>     am <- fresh a (d ::: KindNum)
>     modifyContext (:< A (nm := Some (TyNum (NumVar am + NumConst k)) ::: KindNum))
>     modifyContext (:< Constraint Given (IsPos (mkVar am)))
>     aty      <- instS id Given Fixed t'
>     (xs, r)  <- checkPat top aty ps
>     return (PatBrace (Just a) k : xs, r)

> checkPat top ty (p : _) =
>     erk $ "checkPat: couldn't match pattern " ++ renderMe p
>                ++ " against type " ++ renderMe ty



> inferPat :: STerm -> [SPatternTerm] ->
>                 Contextual () ([PatternTerm], Term ::: Rho, Rho)

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
>     cty  <- existentialise $ instS (++ "_pat_inst") Given Hole sc
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
>     erk $ "inferPat: couldn't infer type of pattern " ++ renderMe p




> traceContext s = getContext >>= \ g -> mtrace (s ++ "\n" ++ renderMe g)