> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts, PatternGuards #-}

> module TypeCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Maybe
> import Data.Bitraversable

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

> goUp :: Type -> Suffix -> ContextualWriter [NormalPredicate] Term Type
> goUp tau _Xi = do
>     st@(St{tValue = t}) <- get
>     case context st of
>       (es :< Layer l) ->
>         case l of         
>             AppLeft () a -> do
>                 put st{tValue = a,
>                     context = es <>< _Xi :< Layer (AppRight (t ::: tau) ())}
>                 inferType
>             AppRight (f ::: sigma) () -> do
>                 put st{tValue = TmApp f t, context = es <>< _Xi}
>                 alpha <- fresh "_t" (Hole ::: Set)
>                 lift $ unify sigma (tau --> TyVar Set alpha)
>                 goUp (TyVar Set alpha) F0
>             LamBody (x ::: sigma) () -> do
>                 put st{tValue = Lam x (bind x t), context = es}
>                 goUp (sigma --> tau) _Xi
>             AnnotLeft () ty -> do
>                 put st{tValue = t :? ty, context = es <>< _Xi}
>                 lift $ unify ty tau
>                 goUp ty F0
>             PatternTop _ _ _ _ -> do
>                 put st{context = context st <>< _Xi}
>                 return tau
>       (es :< A e) -> do
>           put st{context = es}
>           goUp tau (e :> _Xi)
>       B0 -> error (  "Ran out of context when going up from " 
>                      ++ (show t) ++ " : " ++ (show tau))



> inferType :: ContextualWriter [NormalPredicate] Term Type
> inferType = getT >>= \ t -> case t of
>     TmVar x -> do
>         sc  <- tyOf <$> lookupTmVar x
>         ty  <- instantiate sc
>         goUp ty F0
>     TmCon c -> do
>         sc  <- lookupTmCon c
>         ty  <- instantiate sc
>         goUp ty F0
>     TmApp f s -> goAppLeft >> inferType
>     Lam x t -> do
>         a <- fresh "a" (Hole ::: Set)
>         goLam (TyVar Set a)
>         inferType
>     t :? ty -> goAnnotLeft >> inferType


> infer :: STerm -> ContextualWriter [NormalPredicate] () (Term ::: Type)
> infer t = inLocation ("in expression " ++ show (prettyHigh t)) $ do
>     t'        <- lift $ scopeCheckTypes t
>     (ty, cs)  <- lift (withT t' $ runWriterT inferType)
>     tell cs
>     return $ t' ::: ty



> inst :: TypeDef -> Type -> ContextualWriter [NormalPredicate] t Type
> inst d (TyApp f s)     = TyApp f <$> inst d s
> inst d (Bind b x k t)  = do
>     beta <- fresh x (d ::: k)
>     inst d (unbind beta t)
> inst d (Qual p t)      = lift (normalisePred p) >>= tell . (: []) >> inst d t
> inst d t               = return t


> specialise :: Type -> Contextual t Type
> specialise t = do
>     (ty, cs) <- runWriterT (inst Fixed t)
>     modifyContext (<><< map Constraint cs)
>     return ty

> instantiate :: Type -> ContextualWriter [NormalPredicate] t Type
> instantiate = inst Hole


> solvePred :: Bool -> [NormalPredicate] -> NormalPredicate ->
>     Contextual t (Maybe NormalPredicate)
> solvePred try hyps p = getContext >>= solvePredIn try hyps p

> solvePredIn :: Bool -> [NormalPredicate] -> NormalPredicate -> Context ->
>     Contextual t (Maybe NormalPredicate)
> solvePredIn try hyps p g = do
>     mtrace $ "solvePredIn: solving " ++ render p -- ++ " in\n" ++ render g ++ "\ngiven ["
>              -- ++ show (fsepPretty hyps) ++ "]"
>     seekTruth hyps p g
>   where
>     seekTruth :: [NormalPredicate] -> NormalPredicate -> Context ->
>         Contextual t (Maybe NormalPredicate)
>     seekTruth hs p B0                                      = deduce hs p
>     seekTruth hs p (g :< Constraint h)                     = seekTruth (h:hs) p g
>     seekTruth hs p (g :< A (a := Some d ::: KindNum))      = do
>         dn <- typeToNum d
>         seekTruth (map (substNormPred a dn) hs) (substNormPred a dn p) g
>     seekTruth hs p (g :< A (a := _ ::: KindNum)) = case findRewrite a hs of
>         Just n   -> seekTruth (map (substNormPred a n) hs) (substNormPred a n p) g
>         Nothing  | a <? p     -> deduce hs p
>                  | otherwise  -> seekTruth (filter (not . (a <?)) hs) p g
>     seekTruth hs p (g :< _) = seekTruth hs p g

>     findRewrite :: TyName -> [NormalPredicate] -> Maybe NormalNum
>     findRewrite a hs = join $ listToMaybe $ map (toRewrite a) hs

>     toRewrite :: TyName -> NormalPredicate -> Maybe NormalNum
>     toRewrite a (IsZero n) = case lookupVariable a n of
>         Just i | i `dividesCoeffs` n  -> Just $ pivot (a, i) n
>         _                             -> Nothing
>     toRewrite a (IsPos _) = Nothing

>     deduce :: [NormalPredicate] -> NormalPredicate -> Contextual t (Maybe NormalPredicate)
>     deduce hs (IsZero n)  | isZero n                 = return Nothing
>     deduce hs (IsPos n)   | Just k <- getConstant n  = 
>         if k >= 0  then  return Nothing
>                    else  fail $ "Impossible constraint 0 <= " ++ show k
>     deduce hs p  | p `elem` hs  = return Nothing
>                  | try          = return $ Just p
>                  | otherwise    = do
>         g <- getContext
>         fail $ "Could not deduce " ++ render p ++ " from [" ++ show (fsepPretty hs)
>                                              ++ "] in context\n" ++ render g

> solvePreds :: Bool -> [NormalPredicate] -> [NormalPredicate] ->
>                   Contextual t [Maybe NormalPredicate]
> solvePreds try hyps = mapM (solvePred try hyps)


> generalise :: [NormalPredicate] -> Type -> Contextual t Type
> generalise ps t = do
>     ps' <- map reifyPred . catMaybes <$> solvePreds True [] ps
>     g <- getContext
>     (g', t') <- help g (ps' /=> t)
>     putContext g'
>     return t'
>   where
>     help g@(_ :< Layer _)                 t = return (g, t)
>     help (g :< A ((an := Some d ::: k)))  t = help g (substTy an d t)
>     help (g :< A ((an := _ ::: k)))       t = help g (Bind All (fst an) k (bind an t))