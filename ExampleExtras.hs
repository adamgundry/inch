{-# LANGUAGE StandaloneDeriving, FlexibleContexts #-}

module ExampleExtras where

import Example

deriving instance Show Nat
deriving instance Show a => Show (Vec a)
deriving instance (Show a, Show b) => Show (Pair a b)
deriving instance Show UNat
deriving instance Show Fin
deriving instance Show Tm
deriving instance Show Tm'
deriving instance Show Shape
deriving instance Show a => Show (FlipVec a)
deriving instance Show a => Show (Ex a)
deriving instance Show (f (g a)) => Show (Comp f g a)
deriving instance Show a => Show (List a)
deriving instance Show q => Show (Quantity q)
deriving instance Show Unit
deriving instance Show Unit2
deriving instance Show Unit3
deriving instance Show NumOrdering
deriving instance Show a => Show (Vec' a)

thirtymk' = thirtymk (*)
l2v = foldr VCons VNil

v2l VNil = []
v2l (VCons x xs) = x : v2l xs