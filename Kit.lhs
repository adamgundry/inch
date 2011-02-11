> {-# LANGUAGE TypeOperators, GADTs, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

> module Kit where

> import Data.Foldable
> import Data.Traversable

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


> data UnifyMode = Unify | Match

> instance Show UnifyMode where
>     show Unify = "unify"
>     show Match = "match"
