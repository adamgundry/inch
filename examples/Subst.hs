{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Subst where

data Fin :: Num -> * where
  FZero :: forall (n :: Num) . 1 <= n => Fin n
  FSuc  :: forall (n :: Num) . Fin n -> Fin (n+1)

data Tm :: Num -> * where
  V :: forall (m :: Num) . Fin m -> Tm m
  L :: forall (m :: Num) . 0 <= m => Tm (m+1) -> Tm m
  A :: forall (m :: Num) . 0 <= m => Tm m -> Tm m -> Tm m

subst :: forall (m n :: Num) . 0 <= n => (pi (w :: Num) . 0 <= w => Fin (w+m) -> Tm (w + n)) -> Tm m -> Tm n
subst s (V i) = s {0} i
subst s (A f a) = A (subst s f) (subst s a)
subst s (L b) = let  s' :: pi (w :: Num) . 0 <= w => Fin (w + m + 1) -> Tm (w + n + 1)
                     s' {w} = s {w + 1}
                in L (subst s' b)

compSub :: forall (l m n :: Num) . 0 <= n => 
    (pi (w :: Num) . 0 <= w => Fin (w+m) -> Tm (w + n)) ->
    (pi (w :: Num) . 0 <= w => Fin (w+l) -> Tm (w + m)) ->
    (pi (w :: Num) . 0 <= w => Fin (w+l) -> Tm (w + n))
compSub s t {w} i = let f :: pi (x :: Num) . 0 <= x => Fin (x+w+m) -> Tm (x+w+n)
                        f {x} = s {x + w}
                    in subst f (t {w} i)

idSub :: forall (n :: Num) . pi (w :: Num) . 0 <= w =>
            Fin (w + n) -> Tm (w + n)
idSub {w} = V