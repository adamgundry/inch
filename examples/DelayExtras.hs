{-# LANGUAGE StandaloneDeriving #-}

module DelayExtras where

import Delay

deriving instance Show a => Show (Tree a)
deriving instance (Show a, Show b) => Show (Pair a b)
deriving instance Show a => Show (D a)