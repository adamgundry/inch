> {-# LANGUAGE TypeOperators, GADTs, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Kit where

> import Data.Foldable
> import Data.Traversable
> import Debug.Trace


> type TyName           = (String, Int)
> type TmName           = String
> type TyConName        = String
> type TmConName        = String



> data S a where
>     S :: a -> S a
>     Z :: S a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> bind :: (Functor f, Eq a) => a -> f a -> f (S a)
> bind x = fmap inS
>   where  inS y | x == y     = Z
>                | otherwise  = S y

> unbind :: Functor f => a -> f (S a) -> f a
> unbind x = fmap unS
>   where  unS Z      = x
>          unS (S a)  = a

> subst :: (Monad m, Eq a) => a -> m a -> m a -> m a
> subst a t = (>>= f)
>   where f b | a == b     = t
>             | otherwise  = return b

> wk :: (Functor m, Monad m) => (a -> m b) -> (S a -> m (S b))
> wk g Z      = return Z
> wk g (S a)  = fmap S (g a)

> data a :=   b  = a :=   b
>     deriving (Eq, Show, Functor, Foldable, Traversable)
> data a :::  b  = a :::  b
>     deriving (Eq, Show, Functor, Foldable, Traversable)
> infix 3 :=
> infix 4 :::

> tmOf :: a ::: b -> a
> tmOf (a ::: _) = a

> tyOf :: a ::: b -> b
> tyOf (_ ::: b) = b



> mtrace :: Monad m => String -> m ()
> mtrace s = trace s (return ()) >>= \ () -> return ()