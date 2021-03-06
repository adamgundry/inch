> {-# LANGUAGE DeriveFunctor, DeriveFoldable #-}

> module Language.Inch.BwdFwd where

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

> (<>>) :: Bwd a -> Fwd a -> Fwd a
> infixl 8 <>>
> B0 <>> ys         = ys
> (xs :< x) <>> ys  = xs <>> (x :> ys)

> trail :: Bwd a -> [a]
> trail B0 = []
> trail (xs :< x) = trail xs ++ [x]


> (<><<) :: Bwd a -> [a] -> Bwd a
> as <><< [] = as
> as <><< (b:bs) = (as :< b) <><< bs

> fwdLength :: Fwd a -> Int
> fwdLength = help 0
>   where
>     help i F0 = i
>     help i (_ :> fs) = help (i+1) fs