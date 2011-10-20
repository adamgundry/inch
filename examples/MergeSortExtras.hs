{-# LANGUAGE StandaloneDeriving #-}

module MergeSortExtras where

import MergeSort

deriving instance Show a => Show (Vec a)
deriving instance Show a => Show (DTree a)
deriving instance Show OVec
deriving instance Show In

l2v :: [a] -> Vec a
l2v = foldr Cons Nil