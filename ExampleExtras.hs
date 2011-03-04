{-# LANGUAGE StandaloneDeriving #-}

module ExampleExtras where

import Example

deriving instance Show Bools
deriving instance Show Nat
deriving instance Show a => Show (Vec a)
deriving instance (Show a, Show b) => Show (Pair a b)
deriving instance Show UNat
deriving instance Show Fin
deriving instance Show Tm
deriving instance Show Tm'
deriving instance Show Shape