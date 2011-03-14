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
>     (dom, cod)  <- splitFun $ Just fty
>     s           <- check dom s
>     traverse (unify cod) mty
>     return $ TmApp f s ::: cod

> checkInfer mty (Lam x t) = do
>     (dom, cod) <- splitFun mty
>     b <- withLayer (LamBody (x ::: dom) ()) $ check cod (unbind x t)
>     return $ Lam x (bind x b) ::: dom --> cod

> checkInfer mty (Let ds t) = do
>     ds <- traverse checkFunDecl ds
>     -- mtrace . ("checkInfer Let:\n" ++) . renderMe =<< getContext
>     t ::: ty <- withLayer (LetBody (map funDeclToBinding ds) ()) $ checkInfer mty t
>     -- mtrace . ("checkInfer Let 2:\n" ++) . renderMe =<< getContext
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


> splitFun :: Maybe Type -> Contextual a (Type, Type)
> splitFun (Just (TyApp (TyApp (TyB Arr) s) t)) = return (s, t)
> splitFun mty = do
>     n <- freshName
>     a <- unknownTyVar $ "_dom" ++ show n ::: Set
>     b <- unknownTyVar $ "_cod" ++ show n ::: Set
>     traverse (unify (a --> b)) mty
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


> generalise :: Type -> [Pattern] -> Contextual t (Type, [Pattern])
> generalise t ps = do
>     g <- getContext
>     (g', tps) <- help g (t, ps)
>     putContext g'
>     return tps
>   where
>     help g@(_ :< Layer FunTop)               tps = return (g, tps)
>     help g@(_ :< Layer (PatternTop _ _ _ _)) tps = return (g, tps)
>     help (g :< A (an := d ::: k)) (t, ps) | an <? t || an <? ps = case d of
>         Exists  -> errBadExistential an t ps
>         Some d  -> help g (replaceTy k an d t, map (replace3 k an d) ps)
>         _       -> help g (Bind All (fst an) k (bind an t), ps)
>     help (g :< A _) tps = help g tps
>     help (g :< Constraint Wanted p)       (t, ps)  = help g (Qual (reifyPred p) t, ps)
>     help (g :< Constraint Given _)        tps      = help g tps
>     help g t = fail $ "ERROR: Can't help " ++ renderMe g





> checkFunDecl :: SFunDeclaration -> Contextual () FunDeclaration

> checkFunDecl (FunDecl s Nothing pats@(Pat xs _ _ : _)) =
>   inLocation (text $ "in declaration of " ++ s) $ withLayer FunTop $ do
>     sty     <- unknownTyVar $ "_sty" ::: Set
>     pattys  <- map tmOf <$> traverse (checkPat True (s ::: sty) sty) pats
>     (ty', pattys') <- generalise sty pattys
>     return $ FunDecl s (Just $ simplifyTy ty') pattys'

> checkFunDecl (FunDecl s (Just st) pats@(Pat xs _ _ : _)) = 
>   inLocation (text $ "in declaration of " ++ s) $ withLayer FunTop $ do
>     sty ::: k <- inLocation (text "in type" <+> prettyHigh st) $ inferKind B0 st
>     unless (k == Set) $ errKindNotSet k
>     sty'  <- instS True id Given Fixed sty
>     pts <- traverse (checkPat False (s ::: sty) sty') pats
>     let ty = tyOf (head pts)
>         pattys = map tmOf pts
>     (ty', pattys') <- generalise ty pattys
>     return $ FunDecl s (Just $ simplifyTy sty) pattys'

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
>     (s, t) <- lift $ splitFun $ Just sat
>     tell ([v ::: s], [])
>     (pts, ty) <- checkPatTerms top t ps
>     return ((PatVar v ::: s) : pts, ty)
>
> checkPatTerms top sat (PatCon c xs : ps) =
>   inLocation (text "in pattern" <+> prettyHigh (PatCon c xs)) $ do
>     sat <- mapPatWriter $ inst True id Fixed sat
>     (s, t) <- lift $ splitFun $ Just sat
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
>     (s, t) <- lift $ splitFun $ Just sat
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