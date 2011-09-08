{-# LANGUAGE StandaloneDeriving, NoMonomorphismRestriction, FlexibleContexts #-}

module RedBlackExtras where

import RedBlack

deriving instance Show a => Show (Ex a)
deriving instance Show Colour
deriving instance Show a => Show (Tree a)
deriving instance Show a => Show (TreeZip a)
deriving instance Show a => Show (ColTree a)
deriving instance Show a => Show (InsProb a)
deriving instance Show a => Show (RBT a)

unEx2 (Ex t)  = t

flatten E           = []
flatten (TR x l r)  = flatten l ++ (x : flatten r)
flatten (TB x l r)  = flatten l ++ (x : flatten r)

memberT       = member compare
insertT x t   = unEx2 (insert compare x t)
build         = foldr insertT E
sort          = flatten . build
blackHeightT  = blackHeight 0 (1+)
deleteT x t   = unEx2 (delete compare x (blackHeightT t) t)