> {-# LANGUAGE DeriveFunctor, DeriveFoldable, TypeOperators, FlexibleContexts,
>              GADTs, RankNTypes, TypeSynonymInstances #-}

> module Context where

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.Foldable
> import qualified Data.Map as Map
> import Data.Traversable

> import BwdFwd
> import Kind
> import Type
> import Syntax hiding (Alternative)
> import Kit
> import Error
> import PrettyPrinter

> type Bindings = Map.Map TmName (Maybe Sigma, Bool)

> data TmLayer  =  PatternTop  {  ptFun          :: TmName ::: Sigma
>                              ,  ptBinds        :: [TmName ::: Sigma]
>                              ,  ptPreds        :: [Predicate]
>                              ,  ptConstraints  :: [Predicate]
>                              }
>                   |  LamBody (TmName ::: Tau) ()
>                   |  LetBindings Bindings
>                   |  LetBody Bindings ()
>                   |  FunTop
>                   |  GenMark

> bindLayerTypes :: (forall k . Var () k -> Type k) -> TmLayer -> TmLayer
> bindLayerTypes g (PatternTop (x ::: ty) bs ps cs) =
>     PatternTop (x ::: substTy g ty)
>                (map (\ (y ::: yty) -> y ::: substTy g yty) bs)
>                (map (fmap (error "bindNExp g")) ps)
>                (map (fmap (error "bindNExp g")) cs)
>                


> data CStatus = Given | Wanted
>   deriving Show


> data TyDef k = Hole | Some (Type k) | Fixed | Exists
>   deriving Show

> instance FV (TyDef k) where
>     a <? Some t = a <? t
>     a <? _      = False


> type TyEntry k = Var () k := TyDef k

> instance FV (TyEntry k) where
>     a <? (b := d) = a <? b || a <? d


> data AnyTyEntry where
>     TE :: TyEntry k -> AnyTyEntry

> instance Show AnyTyEntry where
>     show (TE t) = show t

> instance FV AnyTyEntry where
>     a <? TE t = a <? t




> data Entry where
>     A           :: TyEntry k -> Entry
>     Layer       :: TmLayer -> Entry
>     Constraint  :: CStatus -> Predicate -> Entry



> defToMaybe :: TyDef k -> Maybe (Type k)
> defToMaybe (Some t)  = Just t
> defToMaybe _         = Nothing

> type Context  = Bwd Entry
> type Suffix   = Fwd AnyTyEntry

> (<><) :: Context -> Suffix -> Context
> _Gamma <>< F0                   = _Gamma
> _Gamma <>< (TE e :> _Xi)  = _Gamma :< A e <>< _Xi
> infixl 8 <><

> data ZipState t = St  {  nextFreshInt :: Int
>                       ,  tValue    :: t
>                       ,  context   :: Context
>                       ,  tyCons    :: Map.Map TyConName (Ex Kind)
>                       ,  tmCons    :: Map.Map TmConName Sigma
>                       ,  bindings  :: Bindings
>                       }


Initial state

> tyInteger   = TyCon "Integer" KSet
> tyBool      = TyCon "Bool" KSet
> tyOrdering  = TyCon "Ordering" KSet
> tyMaybe     = TyApp (TyCon "Maybe" (KSet :-> KSet))
> tyEither a b  = TyApp (TyApp (TyCon "Either" (KSet :-> KSet :-> KSet)) a) b

> initialState = St 0 () B0 initTyCons initTmCons initBindings
> initTyCons = Map.fromList $
>   ("Bool",     Ex KSet) :
>   ("Integer",  Ex KSet) :
>   ("String",   Ex KSet) :
>   ("Maybe",    Ex (KSet :-> KSet)) :
>   ("Ordering",  Ex KSet) :
>   ("Either",    Ex (KSet :-> KSet :-> KSet)) :
>   []
> initTmCons = Map.fromList $
>   ("True",     tyBool) :
>   ("False",    tyBool) :
>   ("Nothing",  Bind All "a" KSet (tyMaybe (TyVar (BVar Top)))) :
>   ("Just",     Bind All "a" KSet
>                    (TyVar (BVar Top) --> (tyMaybe (TyVar (BVar Top))))) :
>   ("LT",       tyOrdering) :
>   ("EQ",       tyOrdering) :
>   ("GT",       tyOrdering) :
>   ("Left",     Bind All "a" KSet (Bind All "b" KSet (TyVar (BVar (Pop Top)) --> tyEither (TyVar (BVar (Pop Top))) (TyVar (BVar Top))))) :
>   ("Right",    Bind All "a" KSet (Bind All "b" KSet (TyVar (BVar Top) --> tyEither (TyVar (BVar (Pop Top))) (TyVar (BVar Top))))) :
>   []
> initBindings = Map.fromList $
>   ("undefined",  (Just (Bind All "a" KSet (TyVar (BVar Top))), True)) :
>   ("id",         (Just (Bind All "a" KSet 
>                           (TyVar (BVar Top) --> TyVar (BVar Top))), True)) :
>   ("compare",    (Just (tyInteger --> tyInteger --> tyOrdering), True)) :
>   []



> type Contextual t a          = StateT (ZipState t) (Either ErrorData) a
> type ContextualWriter w t a  = WriterT w (StateT (ZipState t) (Either ErrorData)) a


Fresh names

> freshVar :: MonadState (ZipState t) m =>
>                 VarState -> String -> Kind k -> m (Var () k)
> freshVar vs s k = do
>     st <- get
>     let beta = nextFreshInt st
>     put st{nextFreshInt = succ beta}
>     return $ FVar (N s beta vs) k

> fresh :: MonadState (ZipState t) m =>
>              VarState -> String -> Kind k -> TyDef k -> m (Var () k)
> fresh vs s k d = do
>     v <- freshVar vs s k
>     modifyContext (:< A (v := d))
>     return v

> unknownTyVar :: (Functor m, MonadState (ZipState t) m) =>
>                     String -> Kind k -> m (Type k)
> unknownTyVar s k = TyVar <$> fresh SysVar s k Hole


T values

> getT :: MonadState (ZipState t) m => m t
> getT = gets tValue

> putT :: MonadState (ZipState t) m => t -> m ()
> putT t = modify $ \ st -> st {tValue = t}

> mapT :: (t -> s) -> (s -> t) -> Contextual s x -> Contextual t x
> mapT f g m = do
>     st <- get
>     case runStateT m st{tValue = f (tValue st)} of
>         Right (x, st') -> put st'{tValue = g (tValue st')} >> return x
>         Left err -> lift $ Left err

> withT :: t -> Contextual t x -> Contextual () x
> withT t = mapT (\ _ -> t) (\ _ -> ())


Context

> getContext :: MonadState (ZipState t) m => m Context
> getContext = gets context
>
> putContext :: MonadState (ZipState t) m => Context -> m ()
> putContext _Gamma = modify $ \ st -> st{context = _Gamma}
>
> modifyContext :: MonadState (ZipState t) m => (Context -> Context) -> m ()
> modifyContext f = getContext >>= putContext . f


Type constructors

> insertTyCon :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                    TyConName -> Ex Kind -> m ()
> insertTyCon x k = do
>     st <- get
>     when (Map.member x (tyCons st)) $ errDuplicateTyCon x
>     put st{tyCons = Map.insert x k (tyCons st)}

> lookupTyCon :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                    TyConName -> m (Ex Kind)
> lookupTyCon x = do
>     tcs <- gets tyCons
>     case Map.lookup x tcs of
>         Just k   -> return k
>         Nothing  -> missingTyCon x


Data constructors

> insertTmCon :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                    TmConName -> Sigma -> m ()
> insertTmCon x ty = do
>     st <- get
>     when (Map.member x (tmCons st)) $ errDuplicateTmCon x
>     put st{tmCons = Map.insert x ty (tmCons st)}

> lookupTmCon :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                     TmConName -> m Sigma
> lookupTmCon x = do
>     tcs <- gets tmCons
>     case Map.lookup x tcs of
>         Just ty  -> return ty
>         Nothing  -> missingTmCon x



Bindings

> lookupBindingIn :: (MonadError ErrorData m) =>
>                    TmName -> Bindings -> m (Term () ::: Sigma, Bool)
> lookupBindingIn x bs = case Map.lookup x bs of
>     Just (Just ty, u)  -> return (TmVar x ::: ty, u)
>     Just (Nothing, _)  -> erk "Mutual recursion requires explicit signatures"
>     Nothing            -> missingTmVar x

> insertBindingIn x ty bs = do
>     when (Map.member x bs) $ errDuplicateTmVar x
>     return $ Map.insert x ty bs

> lookupTopBinding :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                    TmName -> m (Term () ::: Sigma, Bool)
> lookupTopBinding x = lookupBindingIn x =<< gets bindings 

> modifyTopBindings :: MonadState (ZipState t) m => (Bindings -> m Bindings) -> m ()
> modifyTopBindings f = do
>     st <- get
>     bs <- f (bindings st)
>     put st{bindings = bs}

> insertTopBinding :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                      TmName -> (Maybe Sigma, Bool) -> m ()
> insertTopBinding x ty = modifyTopBindings $ insertBindingIn x ty

> updateTopBinding :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                      TmName -> (Maybe Sigma, Bool) -> m ()
> updateTopBinding x ty = modifyTopBindings (return . Map.insert x ty)





> lookupBinding x = help =<< getContext
>   where
>     help B0                             = lookupTopBinding x
>     help (g :< Layer (LetBindings bs))  = lookupBindingIn x bs
>     help (g :< _)                       = help g

> modifyBindings :: (Bindings -> Contextual () Bindings) -> Contextual () ()
> modifyBindings f = flip help [] =<< getContext
>   where
>     help :: Context -> [Entry] -> Contextual () ()
>     help B0 _ = modifyTopBindings f
>     help (g :< Layer (LetBindings bs)) h = do
>         bs' <- f bs
>         putContext $ (g :< Layer (LetBindings bs')) <><< h
>     help (g :< e) h = help g (e:h)

> insertBinding x ty = modifyBindings $ insertBindingIn x ty
> updateBinding x ty = modifyBindings $ return . Map.insert x ty



> {-
> seekTy :: Context -> TyName -> Ex Type
> seekTy (g :< A (b := d ::: k))  a | a == b  = case d of  Some t  -> t
>                                                          _       -> TyVar (FVar b k)
> seekTy (g :< _)                 a           = seekTy g a
> seekTy B0                       a           = error "seekTy: missing!"
> -}

> expandContext :: Context -> Context
> expandContext B0 = B0
> expandContext (g :< A (a := Some t))  = expandContext g
> expandContext (g :< a@(A _))          = expandContext g :< a
> expandContext (g :< Constraint s p)   =
>     expandContext g :< Constraint s (fmap (substTy (expandTyVar g)) p)
> expandContext (g :< Layer l) =
>     expandContext g :< Layer (bindLayerTypes (expandTyVar g) l)


> expandTyVar :: Context -> Var () k -> Type k
> expandTyVar g a = case seek g a of
>     Some d  -> expandType g d
>     _       -> TyVar a
>   where
>     seek (g :< A (b := d))  a = hetEq a b d (seek g a)
>     seek (g :< _)           a           = seek g a
>     seek B0                 a           = error "expandTyVar: erk"

> expandType :: Context -> Type k -> Type k
> expandType g = substTy (expandTyVar g)
    
> expandPred :: Context -> Predicate -> Predicate
> expandPred g = fmap (expandType g)

> niceType :: Type KSet -> Contextual t (Type KSet)
> niceType t = (\ g -> simplifyTy (expandType g t)) <$> getContext

> nicePred :: Predicate -> Contextual t Predicate
> nicePred p = (\ g -> simplifyPred (expandPred g p)) <$> getContext




> lookupTyVar :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                    Binder -> Bwd (Ex (Var ())) -> String -> m (Ex (Var ()))
> lookupTyVar b (g :< Ex a) x
>     | varNameEq a x  = checkBinder b a >> return (Ex a)
>     | otherwise      = lookupTyVar b g x
> lookupTyVar b B0 x = getContext >>= seek
>   where
>     seek B0 = missingTyVar x
>     seek (g :< A (a := _)) | varNameEq a x = checkBinder b a >> return (Ex a)
>     seek (g :< _) = seek g

> checkBinder :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                    Binder -> Var () k -> m ()
> checkBinder All  _  = return ()
> checkBinder Pi   a  = case (varKind a, varBinder a) of
>                         (KNum, Just Pi)  -> return ()
>                         (KNum, _)        -> errBadBindingLevel a
>                         _                -> errNonNumericVar a


> lookupTmVar :: (Alternative m, MonadState (ZipState t) m, MonadError ErrorData m) =>
>                    TmName -> m (Term () ::: Sigma)
> lookupTmVar x = getContext >>= seek
>   where
>     seek B0 = fst <$> lookupTopBinding x
>     seek (g :< Layer (LamBody (y ::: ty) ()))
>         | x == y = return $ TmVar y ::: ty
>     seek (g :< Layer (LetBody bs ()))   = (fst <$> lookupBindingIn x bs) <|> seek g
>     seek (g :< Layer (LetBindings bs))  = (fst <$> lookupBindingIn x bs) <|> seek g
>     seek (g :< Layer (PatternTop (y ::: ty) bs ps cs))
>         | x == y = return $ TmVar y ::: ty
>         | otherwise = case lookIn bs of
>             Just tt  -> return tt
>             Nothing  -> seek g
>     seek (g :< _) = seek g
>
>     lookIn [] = Nothing
>     lookIn ((y ::: ty) : bs)  | x == y     = Just $ TmVar y ::: ty
>                               | otherwise  = lookIn bs




> normaliseNumCx :: Type KNum -> Contextual t NormalNum
> normaliseNumCx = normaliseNum $ \ t -> case t of
>     TyApp (TyApp (BinOp o) m) n -> do
>         a <- fresh SysVar "_nunc" KNum Hole
>         modifyContext (:< Constraint Wanted (Op o m n (TyVar a)))
>         return a
>     _ -> erk $ "normaliseNumCx: cannot normalise " ++ renderMe (fogSysTy t)

> normalisePredCx ::  Predicate -> Contextual t NormalPredicate
> normalisePredCx = traverse normaliseNumCx
