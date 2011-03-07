> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts, PatternGuards #-}

> module TypeCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Maybe
> import Data.Traversable

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

> goUp :: [Entry] -> Contextual (Term, Maybe Type) Type
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



> subsCheck :: Type -> Type -> Contextual a Type
> subsCheck s t = do
>     t  <- specialise t
>     s  <- instantiate s
>     unify s t
>     return t


> inferType :: Contextual (Term, Maybe Type) Type
> inferType = getT >>= \ (t, mty) -> case t of
>     TmVar x -> do
>         sc  <- tyOf <$> lookupTmVar x
>         ty <- case mty of
>             Just ity  -> subsCheck sc ity
>             Nothing   -> instantiate sc
>         putT (t, Just ty)
>         goUp []
>     TmCon c -> do
>         sc  <- lookupTmCon c
>         ty <- case mty of
>             Just ity  -> subsCheck sc ity
>             Nothing   -> instantiate sc
>         putT (t, Just ty)
>         goUp []
>     TmApp f s  -> goAppLeft    >> inferType
>     Lam x t    -> goLam        >> inferType
>     t :? ty    -> goAnnotLeft  >> inferType
>     TmBrace n  -> fail "Braces aren't cool"

> infer :: STerm -> Contextual () (Term ::: Type)
> infer t = inLocation ("in expression " ++ show (prettyHigh t)) $ do
>     t'  <- scopeCheckTypes t
>     ty  <- withT (t', Nothing) $ inferType
>     return $ t' ::: ty

> check :: Type -> STerm -> Contextual () Term
> check ty t = inLocation ("in expression " ++ show (prettyHigh t)) $ do
>     t'  <- scopeCheckTypes t
>     withT (t', Just ty) $ inferType
>     return t'


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
>     collect (g :< Layer (PatternTop _ _ ks ws)) hs ps = 
>         collect g (ks ++ hs) (ws ++ ps)
>     collect (g :< e) hs ps = collect g hs ps <:< e
>
>     (g, a, b) <:< e = (g :< e, a, b)
>
>     want :: [NormalPredicate] -> Contextual t ()
>     want [] = return ()
>     want (p:ps) | nonsense p  = fail $ "Impossible constraint " ++ render p
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
>     help (g :< A ((an := Some d ::: k)))  t = help g (substTy an d t)
>     help (g :< A ((an := _ ::: k)))    t = help g (Bind All (fst an) k (bind an t))
>     help (g :< Constraint Wanted p)       t = help g (Qual (reifyPred p) t)
>     help (g :< Constraint Given _)        t = help g t