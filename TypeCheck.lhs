> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts, PatternGuards #-}

> module TypeCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
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

> goUp :: Type -> Suffix -> ContextualWriter [Predicate] Term Type
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



> inferType :: ContextualWriter [Predicate] Term Type
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


> infer :: STerm -> ContextualWriter [Predicate] () (Term ::: Type)
> infer t = inLocation ("in expression " ++ show (prettyHigh t)) $ do
>     t'        <- lift $ scopeCheckTypes t
>     (ty, cs)  <- lift (withT t' $ runWriterT inferType)
>     tell cs
>     return $ t' ::: ty



> inst :: TypeDef -> Type -> ContextualWriter [Predicate] t Type
> inst d (TyApp f s)     = TyApp f <$> inst d s
> inst d (Bind b x k t)  = do
>     beta <- fresh x (d ::: k)
>     inst d (unbind beta t)
> inst d (Qual p t)      = tell [p] >> inst d t
> inst d t               = return t


> specialise :: Type -> Contextual t Type
> specialise t = do
>     (ty, cs) <- runWriterT (inst Fixed t)
>     modifyContext (<><< map Constraint cs)
>     return ty

> instantiate :: Type -> ContextualWriter [Predicate] t Type
> instantiate = inst Hole


> solvePred :: Bool -> Predicate -> Contextual t Bool
> solvePred try p = getContext >>= solvePredIn try p

> solvePredIn :: Bool -> Predicate -> Context -> Contextual t Bool
> solvePredIn try p g = do
>     p' <- nicePred p
>     mtrace $ "solvePredIn: solving " ++ render p' ++ " in " ++ render (expandContext g)
>     case p of
>         n :<=: m -> normaliseNum (m - n) >>= seekTruth g []
>         n :==: m  | try        -> return False
>                   | otherwise  -> unifyNum n m >> return True
>   where
>     seekTruth :: Context -> [NormalNum] -> NormalNum -> Contextual t Bool
>     seekTruth B0 ns m = deduce m ns
>     seekTruth (g :< Constraint (i :<=: j)) ns m = do
>         n <- normaliseNum $ j - i
>         seekTruth g (n:ns) m             
>     seekTruth (g :< A (a := Some d ::: KindNum)) ns m = do
>         dn <- typeToNum d
>         seekTruth g (map (substNum a dn) ns) (substNum a dn m)
>     seekTruth (g :< A (a := _ ::: KindNum)) ns m = case lookupVariable a m of
>         Just _   -> deduce m ns
>         Nothing  -> seekTruth g ns m
>     seekTruth (g :< _) ns m = seekTruth g ns m

>     deduce :: NormalNum -> [NormalNum] -> Contextual t Bool
>     deduce m ns | Just k <- getConstant m =
>         if k >= 0  then  return True
>                    else  fail $ "Impossible constraint 0 <= " ++ show k
>     deduce m ns | m `elem` ns  = return True
>                 | try          = return False
>                 | otherwise    = fail $
>       "Could not solve constraint 0 <= " ++ render m

> solvePreds try = mapM (solvePred try)


> generalise :: Type -> Contextual t Type
> generalise t = do
>     g <- getContext
>     (g', t') <- help g t
>     putContext g'
>     return t'
>   where
>     help (g :< Layer FunTop) t                  = return (g, t)
>     help (g :< A (((a, n) := Some d ::: k))) t  = help g (substTy (a, n) d t)
>     help (g :< A (((a, n) := _ ::: k))) t       = help g (Bind All a k (bind (a, n) t))
>     help (g :< Constraint p) t                  = do
>         b <- solvePredIn True p g
>         if b then help g t else help g (Qual p t)
