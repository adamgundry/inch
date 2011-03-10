> {-# LANGUAGE TypeOperators, GADTs, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Kit where

> import Control.Applicative
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
>   deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

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

> wk :: Applicative f => (a -> f b) -> (S a -> f (S b))
> wk g Z      = pure Z
> wk g (S a)  = fmap S (g a)


Really we want g to be a pointed functor!

> wkwk :: (Applicative f, Functor g) =>
>     (S b -> g (S b)) -> (a -> f (g b)) -> (S a -> f (g (S b)))
> wkwk p g Z      = pure $ p Z
> wkwk p g (S a)  = fmap S <$> g a


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

> unzipAsc :: [(a ::: b)] -> ([a] ::: [b])
> unzipAsc xs = map tmOf xs ::: map tyOf xs



> mtrace :: Monad m => String -> m ()
> mtrace s = trace s (return ()) >>= \ () -> return ()



> newtype Id a = Id {unId :: a}
>     deriving (Functor, Foldable, Traversable)

> instance Applicative Id where
>     pure = Id
>     Id f <*> Id s = Id (f s)