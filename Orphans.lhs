> module Orphans where

> import Control.Applicative
> import Control.Monad.Error
> import Control.Monad.State
> import Control.Monad.Writer
> import Text.ParserCombinators.Parsec

> instance Monad m => Applicative (StateT s m) where
>     pure = return
>     (<*>) = ap

> instance (Monoid o, Monad m) => Applicative (WriterT o m) where
>     pure = return
>     (<*>) = ap

> instance Applicative (GenParser s a) where
>    pure  = return
>    (<*>) = ap

> instance Alternative (GenParser s a) where
>    empty = mzero
>    (<|>) = mplus

> instance Error a => Applicative (Either a) where
>     pure = return
>     (<*>) = ap