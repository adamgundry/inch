{-# LANGUAGE StandaloneDeriving, FlexibleInstances, DeriveFunctor #-}

module WiresExtras where

import Wires

deriving instance Show a => Show (Vec a)
deriving instance Show (Wire Bool Bool)
deriving instance Functor Vec

instance Show a => Show (Bool -> a) where
    show f = "(True -> " ++ show (f True) ++ "; False -> " ++ show (f False) ++ ")"

btoc True   = '1'
btoc False  = '0'

ctob '0' = False
ctob '1' = True

vtol :: Vec a -> [a]
vtol VNil = []
vtol (VCons x xs) = x : vtol xs

ltov :: [a] -> Vec a
ltov []      = VNil
ltov (x:xs)  = VCons x (ltov xs)

vtob = vtol . fmap btoc
btov = fmap ctob . ltov


lem _ _ = id

test' m p k = vtob $ run p $ toBin m k