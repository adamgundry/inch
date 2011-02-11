> {-# LANGUAGE DeriveFunctor, DeriveFoldable, TypeOperators #-}

> module Context where

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


> data Ent a x  =  A      (TyEnt a)
>               |  Layer  (TmLayer a x)
>               |  Data   TyConName Kind [Con a]
>               |  Func   x (Ty a)
>   deriving Show

> type TyEnt a = a := Maybe (Ty a) ::: Kind

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
>                       ,  dataCons :: Map.Map TmConName Type
>                       }

> initialState = St 0 () B0 Map.empty Map.empty

> type Contextual t a = StateT (ZipState t) (Either ErrorData) a

> getT :: Contextual t t
> getT = gets tValue

> putT :: t -> Contextual t ()
> putT t = modify $ \ st -> st {tValue = t}

> mapT :: (t -> s) -> (s -> t) -> Contextual s x -> Contextual t x
> mapT f g m = do
>     st <- get
>     case runStateT m (st {tValue = f (tValue st)}) of
>         Right (x, st') -> put (st' {tValue = g (tValue st')}) >> return x
>         Left err -> lift $ Left err

> withT :: t -> Contextual t x -> Contextual () x
> withT t = mapT (\ _ -> t) (\ _ -> ())

> getContext :: Contextual t Context
> getContext = gets context
>
> putContext :: Context -> Contextual t ()
> putContext _Gamma = modify $ \ st -> st {context = _Gamma}
>
> modifyContext :: (Context -> Context) -> Contextual t ()
> modifyContext f = getContext >>= putContext . f

> freshName :: Contextual t Int
> freshName = do  st <- get
>                 let beta = nextFreshInt st
>                 put (st {nextFreshInt = succ beta})
>                 return beta

> fresh :: String -> Maybe Type ::: Kind -> Contextual t TyName
> fresh a d = do  beta <- freshName
>                 modifyContext (:< A ((a, beta) := d))
>                 return (a, beta)