> {-# LANGUAGE DeriveFunctor, DeriveFoldable #-}

> module BwdFwd where

> import Data.Foldable
> import Data.Monoid

> data Fwd a = F0 | a :> Fwd a
>     deriving (Eq, Show, Functor, Foldable)

> data Bwd a = B0 | Bwd a :< a
>     deriving (Eq, Show, Functor, Foldable)

> infixr 8 :>
> infixl 8 :<

> instance Monoid (Fwd a) where
>     mempty = F0
>     F0         `mappend` ys = ys
>     (x :> xs)  `mappend` ys = x :> (xs `mappend` ys)

> (<+>) :: Monoid a => a -> a -> a
> (<+>) = mappend

> (<>>) :: Bwd a -> Fwd a -> Fwd a
> infixl 8 <>>
> B0 <>> ys         = ys
> (xs :< x) <>> ys  = xs <>> (x :> ys)

> trail :: Bwd a -> [a]
> trail B0 = []
> trail (xs :< x) = trail xs ++ [x]