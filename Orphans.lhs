> module Orphans where

> import Control.Applicative
> import Control.Monad.State
> import Text.ParserCombinators.Parsec

> instance Monad m => Applicative (StateT s m) where
>     pure = return
>     (<*>) = ap

> instance Applicative (GenParser s a) where
>    pure  = return
>    (<*>) = ap

> instance Alternative (GenParser s a) where
>    empty = mzero
>    (<|>) = mplus