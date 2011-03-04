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

> goLam :: MonadState (ZipState Term) m => Type -> m ()
> goLam tau = modify $ \ st@(St{tValue = Lam x t}) ->
>     st {  tValue = unbind x t
>        ,  context = context st :< Layer (LamBody (x ::: tau) ())
>        }


If the current term is an application, |goAppLeft| enters the
function.

> goAppLeft :: MonadState (ZipState Term) m => m ()
> goAppLeft = modify $ \ st@(St{tValue = TmApp f s}) ->
>     st {tValue = f, context = context st :< Layer (AppLeft () s)}


If the current term is an annotation, |goAnnotLeft| enters the term
being annotated.

> goAnnotLeft :: MonadState (ZipState Term) m => m ()
> goAnnotLeft = modify $ \ st@(St{tValue = t :? ty}) ->
>     st {tValue = t, context = context st :< Layer (AnnotLeft () ty)}


The function |goUp tau _Xi| is called when the term at the current
location has been given type |tau|, and it proceeds up and then right
to find the next type inference problem.

The accumulator |_Xi| collects variable definitions that |tau| may
depend on, and hence must be reinserted into the context once the new
location is found.

> goUp :: Type -> [Entry] -> Contextual Term Type
> goUp tau _Xi = do
>     st@(St{tValue = t}) <- get
>     case context st of
>       (es :< Layer l) ->
>         case l of         
>             AppLeft () (TmBrace n) -> do
>                 put st{tValue = TmApp t (TmBrace n),
>                     context = es <><< _Xi}
>                 case tau of
>                     Bind Pi x KindNum t -> do
>                         nm <- fresh "_n" (Some (TyNum n) ::: KindNum)
>                         t' <- instantiate (unbind nm t)
>                         goUp t' []
>             AppLeft () a -> do
>                 put st{tValue = a,
>                     context = es <><< _Xi :< Layer (AppRight (t ::: tau) ())}
>                 inferType
>             AppRight (f ::: sigma) () -> do
>                 put st{tValue = TmApp f t, context = es <><< _Xi}
>                 alpha <- fresh "_t" (Hole ::: Set)
>                 unify sigma (tau --> TyVar Set alpha)
>                 goUp (TyVar Set alpha) []
>             LamBody (x ::: sigma) () -> do
>                 put st{tValue = Lam x (bind x t), context = es}
>                 goUp (sigma --> tau) _Xi
>             AnnotLeft () ty -> do
>                 put st{tValue = t :? ty, context = es <><< _Xi}
>                 unify ty tau
>                 goUp ty []
>             PatternTop _ _ _ _ -> do
>                 put st{context = context st <><< _Xi}
>                 return tau
>       (es :< e) -> do
>           put st{context = es}
>           goUp tau (e : _Xi)
>       B0 -> error (  "Ran out of context when going up from " 
>                      ++ (show t) ++ " : " ++ (show tau))



> inferType :: Contextual Term Type
> inferType = getT >>= \ t -> case t of
>     TmVar x -> do
>         sc  <- tyOf <$> lookupTmVar x
>         ty  <- instantiate sc

>         -- g <- expandContext <$> getContext
>         -- mtrace $ "inferType " ++ x ++ " :: " ++ render ty ++ "\n" ++ render g

>         goUp ty []
>     TmCon c -> do
>         sc  <- lookupTmCon c
>         ty  <- instantiate sc
>         goUp ty []
>     TmApp f s -> goAppLeft >> inferType
>     TmBrace n -> fail "Braces aren't cool"
>     Lam x t -> do
>         a <- fresh "_a" (Hole ::: Set)
>         goLam (TyVar Set a)
>         inferType
>     t :? ty -> goAnnotLeft >> inferType


> infer :: STerm -> Contextual () (Term ::: Type)
> infer t = inLocation ("in expression " ++ show (prettyHigh t)) $ do
>     t'  <- scopeCheckTypes t
>     ty  <- withT t' $ inferType
>     return $ t' ::: ty



> inst :: (String -> String) -> TypeDef -> Type -> ContextualWriter [NormalPredicate] t Type
> inst s d (TyApp f a)     = TyApp f <$> inst s d a
> inst s d (Bind All x k t)  = do
>     beta <- fresh (s x) (d ::: k)
>     inst s d (unbind beta t)
> inst s d (Qual p t)      = do
>     p' <- lift $ normalisePred p
>     tell [p']
>     inst s d t
> inst s d t               = return t


> instS :: (String -> String) -> CStatus -> TypeDef -> Type -> Contextual t Type
> instS f s d t = do
>     (ty, cs) <- runWriterT $ inst f d t
>     modifyContext (<><< map (Constraint s) cs)
>     return ty


> specialise :: Type -> Contextual t Type
> specialise = instS id Given Fixed

> instantiate :: Type -> Contextual t Type
> instantiate = instS (++ "_inst") Wanted Hole


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