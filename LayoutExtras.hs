{-# LANGUAGE StandaloneDeriving, DeriveFunctor, FlexibleInstances #-}

module LayoutExtras where

import Layout

deriving instance (Show a, Show b) => Show (Pair a b)
deriving instance Show a => Show (Option a)
deriving instance Functor Option
deriving instance Show a => Show (Ex a)
deriving instance (Show a, Show b) => Show (Ex2 a b)

deriving instance Show Ident
deriving instance Show Max
deriving instance Show a => Show (K a)
deriving instance Show a => Show (Layout a)
deriving instance Show a => Show (Vec a)
deriving instance Show a => Show (LContext a)
deriving instance Show a => Show (LZip a)
deriving instance (Show x, Show y, Show p) => Show (VP x y p)
-- deriving instance (Show x, Show y, Show p) => Show (MoreVP x y p)

instance Monad Option where
  return = Some
  (Some x) >>= f = f x
  None     >>= f = None

showVOI :: Vec (Option Ident) -> String
showVOI Nil = ""
showVOI (Cons None xs) = ' ' : showVOI xs
showVOI (Cons (Some i) xs) = show i ++ showVOI xs

instance Show (M (Option Ident)) where
  show (M Nil) = ""
  show (M (Cons x xs)) = showVOI x ++ "\n" ++ show (M xs)

renderS w d = putStrLn . show . render w d

unEx (Ex a) = a
fstEx2 (Ex2 a _) = a
sndEx2 (Ex2 _ a) = a


instance Functor Layout where
  fmap = mapLayout

instance Monad Layout where
  (>>=)   = flip bindLayout
  return  = returnLayout