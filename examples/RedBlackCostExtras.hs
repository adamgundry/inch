{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}

module RedBlackCostExtras where

import RedBlackCost

deriving instance Show Colour
deriving instance Show a => Show (Tree a)
deriving instance Show a => Show (TreeZip a)
deriving instance Show a => Show (ColTree a)
deriving instance Show a => Show (InsProb a)
deriving instance Show a => Show (RBT a)

flatten E           = []
flatten (TR x l r)  = flatten l ++ (x : flatten r)
flatten (TB x l r)  = flatten l ++ (x : flatten r)

flattenRBT (RBT t) = flatten t

memberT x t   = member compare x t
insertT x t   = insert compare x t
build xs      = foldr insertT empty xs
sort xs       = flattenRBT (build xs)
deleteT x t   = delete compare x t
