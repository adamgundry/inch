> {-# LANGUAGE DeriveFunctor, DeriveFoldable, TypeOperators #-}

> module Context where

> import Control.Monad.Error ()
> import Control.Monad.State
> import Data.Foldable
> import Data.Monoid

> import BwdFwd
> import Syntax


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
> type ZipState t = (Int, t, Context)

> type Suffix = Fwd TyEntry

> (<><) :: Context -> Suffix -> Context
> _Gamma <>< F0                   = _Gamma
> _Gamma <>< (e :> _Xi)  = _Gamma :< A e <>< _Xi
> infixl 8 <><


> type Contextual t a = StateT (ZipState t) (Either String) a

> getT :: Contextual t t
> getT = do  (_, t, _) <- get
>            return t

> putT :: t -> Contextual t ()
> putT t = do  (beta, _, _Gamma) <- get
>              put (beta, t, _Gamma)

> mapT :: (t -> s) -> (s -> t) -> Contextual s x -> Contextual t x
> mapT f g m = do
>     (beta, t, _Gamma) <- get
>     case runStateT m (beta, f t, _Gamma) of
>         Right (x, (beta', t', _Gamma')) -> put (beta', g t', _Gamma') >> return x
>         Left err -> lift $ Left err

> withT :: t -> Contextual t x -> Contextual () x
> withT t = mapT (\ _ -> t) (\ _ -> ())

> getContext :: Contextual t Context
> getContext = do  (_, _, _Gamma) <- get
>                  return _Gamma
>
> putContext :: Context -> Contextual t ()
> putContext _Gamma = do  (beta,  t, _) <- get
>                         put (beta, t, _Gamma)
>
> modifyContext :: (Context -> Context) -> Contextual t ()
> modifyContext f = getContext >>= putContext . f

> freshName :: Contextual t Int
> freshName = do  (beta, t, _Gamma) <- get
>                 put (succ beta, t, _Gamma)
>                 return beta

> fresh :: String -> Maybe Type ::: Kind -> Contextual t TyName
> fresh a d = do  beta <- freshName
>                 modifyContext (:< A ((a, beta) := d))
>                 return (a, beta)