{-# LANGUAGE StandaloneDeriving #-}

module ExampleExtras where

import Example

deriving instance Show Bools
deriving instance Show Nat
deriving instance Show a => Show (Vec a)
deriving instance Show UNat
deriving instance Show Fin
deriving instance Show Tm