> {-# LANGUAGE DeriveFunctor, DeriveFoldable, TypeOperators #-}

> module Context where

> import Control.Applicative
> import Control.Monad.Error ()
> import Control.Monad.State
> import Data.Foldable
> import Data.Monoid
> import qualified Data.Map as Map

> import BwdFwd
> import Syntax
> import Kit
> import Error


> data TmLayer a x  =  PatternTop (x ::: Ty a) [x ::: Ty a]
>                   |  AppLeft () (Tm a x)
>                   |  AppRight (Tm a x ::: Ty a) ()
>                   |  LamBody (x ::: Ty a) ()
>                   |  AnnotLeft () (Ty a)
>                   |  FunTop
>     deriving (Eq, Show)

> type TermLayer = TmLayer TyName TmName


> type TyEnt a = a := TyDef a ::: Kind

> data Ent a x  =  A      (TyEnt a)
>               |  Layer  (TmLayer a x)
>               |  Func   x (Ty a)
>               |  Constraint (Pred a)
>   deriving Show

> data TyDef a = Hole | Some (Ty a) | Fixed
>   deriving (Show, Functor, Foldable)

> defToMaybe :: TyDef a -> Maybe (Ty a)
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

> type Contextual t a = StateT (ZipState t) (Either ErrorData) a


Fresh names

> freshName :: Contextual t Int
> freshName = do  st <- get
>                 let beta = nextFreshInt st
>                 put st{nextFreshInt = succ beta}
>                 return beta

> fresh :: String -> TypeDef ::: Kind -> Contextual t TyName
> fresh a d = do  beta <- freshName
>                 modifyContext (:< A ((a, beta) := d))
>                 return (a, beta)


T values

> getT :: Contextual t t
> getT = gets tValue

> putT :: t -> Contextual t ()
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

> getContext :: Contextual t Context
> getContext = gets context
>
> putContext :: Context -> Contextual t ()
> putContext _Gamma = modify $ \ st -> st{context = _Gamma}
>
> modifyContext :: (Context -> Context) -> Contextual t ()
> modifyContext f = getContext >>= putContext . f


Type constructors

> insertTyCon :: TyConName -> Kind -> Contextual t ()
> insertTyCon x k = do
>     st <- get
>     when (Map.member x (tyCons st)) $ errDuplicateTyCon x
>     put st{tyCons = Map.insert x k (tyCons st)}

> lookupTyCon :: TyConName -> Contextual t Kind
> lookupTyCon x = do
>     tcs <- gets tyCons
>     case Map.lookup x tcs of
>         Just k   -> return k
>         Nothing  -> missingTyCon x


Data constructors

> insertTmCon :: TmConName -> Type -> Contextual t ()
> insertTmCon x ty = do
>     st <- get
>     when (Map.member x (tmCons st)) $ errDuplicateTmCon x
>     put st{tmCons = Map.insert x ty (tmCons st)}

> lookupTmCon :: TmConName -> Contextual t Type
> lookupTmCon x = do
>     tcs <- gets tmCons
>     case Map.lookup x tcs of
>         Just ty  -> return ty
>         Nothing  -> missingTmCon x



> normaliseType :: Type -> Contextual t Type
> normaliseType t = do
>     g <- getContext
>     return $ simplifyTy $ t >>= normalTyVar g
>   where
>     normalTyVar :: Context -> TyName -> Type
>     normalTyVar g a = maybe (TyVar a) (>>= normalTyVar g) $ defToMaybe $ seek g a

>     seek B0 a = error "normaliseType: erk"
>     seek (g :< A (b := d ::: _)) a | a == b = d
>     seek (g :< _) a = seek g a