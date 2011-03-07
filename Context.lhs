> {-# LANGUAGE DeriveFunctor, DeriveFoldable, TypeOperators, FlexibleContexts #-}

> module Context where

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.State
> import Control.Monad.Writer
> import Data.Foldable
> import Data.Monoid
> import qualified Data.Map as Map

> import BwdFwd
> import TyNum
> import Type
> import Syntax
> import Kit
> import Error


> data TmLayer a x  =  PatternTop  {  ptFun    :: x ::: Ty Kind a
>                                  ,  ptBinds  :: [x ::: Ty Kind a]
>                                  ,  ptPreds  :: [NormPred a]
>                                  ,  ptConstraints :: [NormPred a]
>                                  }
>                   |  AppLeft () (Tm Kind a x) (Maybe (Ty Kind a))
>                   |  AppRight (Tm Kind a x ::: Ty Kind a) ()
>                   |  LamBody (x ::: Ty Kind a) ()
>                   |  AnnotLeft () (Ty Kind a)
>                   |  FunTop
>     deriving (Eq, Show)

> type TermLayer = TmLayer TyName TmName

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



> data CStatus = Given | Wanted
>   deriving Show

> type TyEnt a = a := TyDef a ::: Kind

> data Ent a x  =  A      (TyEnt a)
>               |  Layer  (TmLayer a x)
>               |  Func   x (Ty Kind a)
>               |  Constraint CStatus (NormPred a)
>   deriving Show

> data TyDef a = Hole | Some (Ty Kind a) | Fixed
>   deriving (Show, Functor, Foldable)

> defToMaybe :: TyDef a -> Maybe (Ty Kind a)
> defToMaybe (Some t)  = Just t
> defToMaybe _         = Nothing

> type TypeDef = TyDef TyName
> type Entry = Ent TyName TmName
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



> seekTy B0 a = error "seekTy: missing!"
> seekTy (g :< A (b := d ::: k)) a | a == b = case d of
>                                               Some t  -> t
>                                               _       -> var k a
> seekTy (g :< _) a = seekTy g a


> expandContext :: Context -> Context
> expandContext B0 = B0
> expandContext (g :< A (a := Some t ::: k))  = expandContext g
> expandContext (g :< a@(A _))                = expandContext g :< a
> expandContext (g :< Constraint s p)           =
>     expandContext g :< Constraint s (bindNormPred (normalNum . toNum . seekTy g) p)
> expandContext (g :< Func x ty) =
>     expandContext g :< Func x (bindTy (\ _ -> seekTy g) ty)
> expandContext (g :< Layer l) =
>     expandContext g :< Layer (bindLayer (\ _ -> seekTy g) l)

> expandType :: Context -> Type -> Type
> expandType g t = bindTy (expandTyVar g) t
>   where
>     expandTyVar :: Context -> Kind -> TyName -> Type
>     expandTyVar g k a = maybe (TyVar k a) (bindTy (expandTyVar g)) $ defToMaybe $ seek g a

>     seek B0 a = error "expandType: erk"
>     seek (g :< A (b := d ::: _)) a | a == b = d
>     seek (g :< _) a = seek g a

> expandNum :: Context -> TypeNum -> TypeNum
> expandNum g n = n >>= expandNumVar g
>   where
>     expandNumVar :: Context -> TyName -> TypeNum
>     expandNumVar g a = maybe (NumVar a) ((>>= expandNumVar g) . toNum) $ defToMaybe $ seek g a

>     seek B0 a = error "expandNum: erk"
>     seek (g :< A (b := d ::: KindNum)) a | a == b = d
>     seek (g :< _) a = seek g a

> expandPred :: Context -> Predicate -> Predicate
> expandPred g (n :<=: m) = expandNum g n :<=: expandNum g m
> expandPred g (n :==: m) = expandNum g n :==: expandNum g m

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
