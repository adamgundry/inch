{-# LANGUAGE StandaloneDeriving #-}

module QueueExtras where

import Queue

deriving instance (Show a, Show b) => Show (Pair a b)
deriving instance Show a => Show (Vec a)
deriving instance Show a => Show (Queue a)
deriving instance Show a => Show (Queue2 a)