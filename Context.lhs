> {-# LANGUAGE DeriveFunctor, DeriveFoldable, TypeOperators, FlexibleContexts #-}

> module Context where

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.State
> import Control.Monad.Writer
> import Data.Foldable
> import Data.Monoid
> import qualified Data.Map as Map
> import Data.Traversable

> import BwdFwd
> import TyNum
> import Type
> import Syntax
> import Kit
> import Error


> data TmLayer k a x  =  PatternTop  {  ptFun  :: x ::: Ty k a
>                                  ,  ptBinds  :: [x ::: Ty k a]
>                                  ,  ptPreds  :: [NormPred a]
>                                  ,  ptConstraints :: [NormPred a]
>                                  }
>                   |  AppLeft () (Tm k a x) (Maybe (Ty k a))
>                   |  AppRight (Tm k a x ::: Ty k a) ()
>                   |  LamBody (x ::: Ty k a) ()
>                   |  LetBody [x ::: Ty k a] ()
>                   |  AnnotLeft () (Ty k a)
>                   |  FunTop
>                   |  GenMark
>     deriving Show

> type TermLayer = TmLayer Kind TyName TmName

> {-
> bindLayer :: (Ord a, Ord b) => (Kind -> a -> Ty Kind b) -> TmLayer a x -> TmLayer b x
> bindLayer f (PatternTop (x ::: t) yts ps cs) =
>     PatternTop (x ::: bindTy f t)
>         (map (\ (y ::: t) -> y ::: bindTy f t) yts)
>         (map (bindNormPred (normalNum . toNum . f KindNum)) ps)
>         (map (bindNormPred (normalNum . toNum . f KindNum)) cs)
> bindLayer f (AppLeft () tm mty)         = AppLeft () (bindTypes f tm) (fmap (bindTy f) mty)
> bindLayer f (AppRight (tm ::: ty) ())   = AppRight (bindTypes f tm ::: bindTy f ty) ()
> bindLayer f (LamBody (x ::: ty) ())     = LamBody (x ::: bindTy f ty) ()
> bindLayer f (AnnotLeft () ty)           = AnnotLeft () (bindTy f ty)
> bindLayer f FunTop                      = FunTop
> -}


> instance Trav3 TmLayer where
>     trav3 fn fa fx (PatternTop b bs hs ps) =
>         PatternTop <$> travBind b
>                    <*> traverse travBind bs
>                    <*> traverse ((normalPred <$>) . travPred fn . reifyPred) hs
>                    <*> traverse ((normalPred <$>) . travPred fn . reifyPred) ps
>       where
>         travBind (x ::: ty) = (:::) <$> fx x <*> fa ty
>     trav3 fn fa fx (AppLeft () tm mty) = AppLeft () <$> trav3 fn fa fx tm
>         <*> maybe (pure Nothing) (fmap Just . fa) mty
>     trav3 fn fa fx FunTop = pure $ FunTop


> data CStatus = Given | Wanted
>   deriving Show

> type TyEnt a = a := TyDef a ::: Kind

> data Ent k a x  =  A      (TyEnt a)
>                 |  Layer  (TmLayer k a x)
>                 |  Func   x (Ty k a)
>                 |  Constraint CStatus (NormPred a)
>   deriving Show

> data TyDef a = Hole | Some (Ty Kind a) | Fixed | Exists
>   deriving (Show, Functor, Foldable)

> defToMaybe :: TyDef a -> Maybe (Ty Kind a)
> defToMaybe (Some t)  = Just t
> defToMaybe _         = Nothing

> type TypeDef = TyDef TyName
> type Entry = Ent Kind TyName TmName
> type TyEntry = TyEnt TyName
> type Context = Bwd Entry
> type Suffix = Fwd TyEntry

> (<><) :: Context -> Suffix -> Context
> _Gamma <>< F0                   = _Gamma
> _Gamma <>< (e :> _Xi)  = _Gamma :< A e <>< _Xi
> infixl 8 <><

> data ZipState t = St  {  nextFreshInt :: Int
>                       ,  tValue :: t
>                       ,  context :: Context
>                       ,  tyCons :: Map.Map TyConName Kind
>                       ,  tmCons :: Map.Map TmConName Type
>                       }

> initialState = St 0 () B0 Map.empty Map.empty

> type Contextual t a          = StateT (ZipState t) (Either ErrorData) a
> type ContextualWriter w t a  = WriterT w (StateT (ZipState t) (Either ErrorData)) a


Fresh names

> freshName :: MonadState (ZipState t) m => m Int
> freshName = do  st <- get
>                 let beta = nextFreshInt st
>                 put st{nextFreshInt = succ beta}
>                 return beta

> freshS :: (Functor m, MonadState (ZipState t) m) => String -> m TyName
> freshS s = (\ n -> (s, n)) <$> freshName

> fresh :: MonadState (ZipState t) m => String -> TypeDef ::: Kind -> m TyName
> fresh a d = do  beta <- freshName
>                 modifyContext (:< A ((a, beta) := d))
>                 return (a, beta)

> unknownTyVar :: (Functor m, MonadState (ZipState t) m) => String ::: Kind -> m Type
> unknownTyVar (s ::: k) = TyVar k <$> fresh s (Hole ::: k)


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
>                    TyConName -> Kind -> m ()
> insertTyCon x k = do
>     st <- get
>     when (Map.member x (tyCons st)) $ errDuplicateTyCon x
>     put st{tyCons = Map.insert x k (tyCons st)}

> lookupTyCon :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                    TyConName -> m Kind
> lookupTyCon x = do
>     tcs <- gets tyCons
>     case Map.lookup x tcs of
>         Just k   -> return k
>         Nothing  -> missingTyCon x


Data constructors

> insertTmCon :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                    TmConName -> Type -> m ()
> insertTmCon x ty = do
>     st <- get
>     when (Map.member x (tmCons st)) $ errDuplicateTmCon x
>     put st{tmCons = Map.insert x ty (tmCons st)}

> lookupTmCon :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                     TmConName -> m Type
> lookupTmCon x = do
>     tcs <- gets tmCons
>     case Map.lookup x tcs of
>         Just ty  -> return ty
>         Nothing  -> missingTmCon x



> seekTy :: Context -> TyName -> Type
> seekTy (g :< A (b := d ::: k))  a | a == b  = case d of  Some t  -> t
>                                                          _       -> var k a
> seekTy (g :< _)                 a           = seekTy g a
> seekTy B0                       a           = error "seekTy: missing!"


> seekNum :: Context -> TyName -> TypeNum
> seekNum (g :< A (b := d ::: KindNum))  a | a == b  = case d of  Some t  -> toNum t
>                                                                 _       -> NumVar a
> seekNum (g :< _)                       a           = seekNum g a
> seekNum B0                             a           = error "seekNum: missing!"


> expandContext :: Context -> Context
> expandContext B0 = B0
> expandContext (g :< A (a := Some t ::: k))  = expandContext g
> expandContext (g :< a@(A _))                = expandContext g :< a
> expandContext (g :< Constraint s p)           =
>     expandContext g :< Constraint s (bindNormPred (normalNum . seekNum g) p)
> expandContext (g :< Func x ty) =
>     expandContext g :< Func x (bindTy (seekNum g) (const $ seekTy g) ty)
> expandContext (g :< Layer l) =
>     expandContext g :< Layer (bind3 (seekNum g) (const $ seekTy g) id l)


> expandTyVar :: Context -> Kind -> TyName -> Type
> expandTyVar g k a = case seek g a of
>     Some d  -> expandType g d
>     _       -> TyVar k a
>   where
>     seek (g :< A (b := d ::: _))  a | a == b  = d
>     seek (g :< _)                 a           = seek g a
>     seek B0                       a           = error "expandTyVar: erk"

> expandType :: Context -> Type -> Type
> expandType g t = bindTy (expandNumVar g) (expandTyVar g) t
    
> expandNum :: Context -> TypeNum -> TypeNum
> expandNum g n = n >>= expandNumVar g

> expandNumVar :: Context -> TyName -> TypeNum
> expandNumVar g a = case seek g a of
>     Some d  -> expandNum g (toNum d)
>     _       -> NumVar a
>   where
>     seek (g :< A (b := d ::: KindNum))  a | a == b  = d
>     seek (g :< _)                       a           = seek g a
>     seek B0                             a           = error "expandNumVar: erk"

> expandPred :: Context -> Predicate -> Predicate
> expandPred g = mapPred (expandNum g)

> niceType :: Type -> Contextual t Type
> niceType t = (\ g -> simplifyTy (expandType g t)) <$> getContext

> nicePred :: Predicate -> Contextual t Predicate
> nicePred p = (\ g -> simplifyPred (expandPred g p)) <$> getContext


> lookupTyVar :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                    Bwd (TyName ::: Kind) -> String -> m (TyName ::: Kind)
> lookupTyVar (g :< ((b, n) ::: k)) a  | a == b     = return $ (a, n) ::: k
>                                      | otherwise  = lookupTyVar g a
> lookupTyVar B0 a = getContext >>= seek
>   where
>     seek B0 = missingTyVar a
>     seek (g :< A ((t, n) := _ ::: k)) | a == t = return $ (t, n) ::: k
>     seek (g :< _) = seek g

> lookupNumVar :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                     Bwd (TyName ::: Kind) -> String -> m TypeNum
> lookupNumVar (g :< ((b, n) ::: k)) a
>     | a == b && k == KindNum  = return $ NumVar (a, n)
>     | a == b                  = errNonNumericVar (a, n)
>     | otherwise               = lookupNumVar g a
> lookupNumVar B0 a = getContext >>= seek
>   where
>     seek B0 = missingNumVar a
>     seek (g :< A ((t, n) := _ ::: k))
>         | a == t && k == KindNum = return $ NumVar (t, n)
>         | a == t = errNonNumericVar (a, n)
>     seek (g :< _) = seek g

> lookupTmVar :: (MonadState (ZipState t) m, MonadError ErrorData m) =>
>                    TmName -> m (Term ::: Type)
> lookupTmVar x = getContext >>= seek
>   where
>     seek B0 = missingTmVar x
>     seek (g :< Func y ty)                      | x == y = return $ TmVar y ::: ty
>     seek (g :< Layer (LamBody (y ::: ty) ()))  | x == y = return $ TmVar y ::: ty
>     seek (g :< Layer (LetBody bs ())) = case lookIn bs of
>                                             Just tt  -> return tt
>                                             Nothing  -> seek g
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
