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

> goUp :: Type -> [Entry] -> Contextual Term Type
> goUp tau _Xi = do
>     st@(St{tValue = t}) <- get
>     case context st of
>       (es :< Layer l) ->
>         case l of         
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
>         goUp ty []
>     TmCon c -> do
>         sc  <- lookupTmCon c
>         ty  <- instantiate sc
>         goUp ty []
>     TmApp f s -> goAppLeft >> inferType
>     Lam x t -> do
>         a <- fresh "a" (Hole ::: Set)
>         goLam (TyVar Set a)
>         inferType
>     t :? ty -> goAnnotLeft >> inferType


> infer :: STerm -> Contextual () (Term ::: Type)
> infer t = inLocation ("in expression " ++ show (prettyHigh t)) $ do
>     t'  <- scopeCheckTypes t
>     ty  <- withT t' $ inferType
>     return $ t' ::: ty



> inst :: TypeDef -> Type -> ContextualWriter [NormalPredicate] t Type
> inst d (TyApp f a)     = TyApp f <$> inst d a
> inst d (Bind b x k t)  = do
>     beta <- fresh x (d ::: k)
>     inst d (unbind beta t)
> inst d (Qual p t)      = do
>     p' <- lift $ normalisePred p
>     tell [p']
>     inst d t
> inst d t               = return t


> instS :: CStatus -> TypeDef -> Type -> Contextual t Type
> instS s d t = do
>     (ty, cs) <- runWriterT $ inst d t
>     modifyContext (<><< map (Constraint s) cs)
>     return ty


> specialise :: Type -> Contextual t Type
> specialise = instS Given Fixed

> instantiate :: Type -> Contextual t Type
> instantiate = instS Wanted Hole


> solveConstraints :: Bool -> Contextual t ()
> solveConstraints try = seekTruth [] []
>  where
>   seekTruth :: [NormalPredicate] -> [NormalPredicate] -> Contextual t ()
>   seekTruth hs ps = do
>     g <- getContext
>     case g of
>       B0         -> do
>           cs <- catMaybes <$> mapM (deduce hs) ps
>           unless (null cs) $ fail "solveConstraints: out of scope error"
>       (g :< xD)  -> putContext g >> case xD of
>           Constraint Given h   -> seekTruth (h:hs) ps
>           Constraint Wanted p  -> seekTruth hs (p:ps)
>           A (a := Some d ::: KindNum) -> do
>               dn <- typeToNum d
>               seekTruth (subs a dn hs) (subs a dn ps)
>               modifyContext (:< xD)
>           A (a := d ::: KindNum) -> case findRewrite a hs of
>               Just n   -> do
>                   seekTruth (subs a n hs) (subs a n ps)
>                   modifyContext (:< xD)
>               Nothing  -> do
>                   let (aps, qs) = partition (a <?) ps
>                   seekTruth (filter (not . (a <?)) hs) qs
>                   modifyContext (:< xD)
>                   cs <- catMaybes <$> mapM (deduce hs) aps
>                   modifyContext (<><< map (Constraint Wanted) cs)
>           Layer (PatternTop _ _ ks ws) -> seekTruth (ks ++ hs) (ws ++ ps)
>           _ -> seekTruth hs ps >> modifyContext (:< xD)


>   subs a dn = map (substNormPred a dn)


>   deduce :: [NormalPredicate] -> NormalPredicate -> Contextual t (Maybe NormalPredicate)
>   deduce hs (IsZero n)  | isZero n                 = return Nothing
>   deduce hs (IsPos n)   | Just k <- getConstant n  = 
>         if k >= 0  then  return Nothing
>                    else  fail $ "Impossible constraint 0 <= " ++ show k
>   deduce hs p  | p `elem` hs  = return Nothing
>                  | try          = return $ Just p
>                  | otherwise    = do
>         g <- getContext
>         fail $ "Could not deduce " ++ render p ++ " from [" ++ show (fsepPretty hs)
>                                              ++ "] in context\n" ++ render g



> generalise :: Type -> Contextual t Type
> generalise t = do
>     g <- getContext
>     (g', t') <- help g t
>     putContext g'
>     return t'
>   where
>     help g@(_ :< Layer FunTop)            t = return (g, t)
>     help (g :< A ((an := Some d ::: k)))  t = help g (substTy an d t)
>     help (g :< A ((an := _ ::: k)))       t = help g (Bind All (fst an) k (bind an t))
>     help (g :< Constraint Wanted p)       t = help g (Qual (reifyPred p) t)