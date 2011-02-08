> {-# LANGUAGE DeriveFunctor, DeriveFoldable, TypeOperators #-}

> module Context where

> import Control.Monad.Error ()
> import Control.Monad.State
> import Data.Foldable
> import Data.Monoid

> import BwdFwd
> import Syntax


> data a :=   b  = a :=   b
>     deriving (Eq, Show, Functor, Foldable)
> data a :::  b  = a :::  b
>     deriving (Eq, Show, Functor, Foldable)
> infix 3 :=
> infix 4 :::

> tmOf :: a ::: b -> a
> tmOf (a ::: _) = a

> tyOf :: a ::: b -> b
> tyOf (_ ::: b) = b


> data TmLayer tyv tmv  =  PatternTop (tmv ::: Ty tyv) [tmv ::: Ty tyv]
>                       |  AppLeft () (Tm tmv)
>                       |  AppRight (Tm tmv ::: Ty tyv) ()
>                       |  LamBody (tmv ::: Ty tyv) ()
>                       |  FunTop
>     deriving (Eq, Show)

> type TermLayer = TmLayer TyName TmName


> data Entry  =  A      TyEntry
>             |  Layer  TermLayer
>             |  Data   TyName Kind [Constructor]
>             |  Func   TmName Type
>   deriving Show

> type TyEntry = TyName := Maybe Type ::: Kind

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