{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

module Queue where

data Pair :: * -> * -> * where
  Pair :: forall a b . a -> b -> Pair a b

p0 (Pair a b) = a
p1 (Pair a b) = b

data Vec :: * -> Num -> * where
  Nil   :: forall a . Vec a 0
  Cons  :: forall (n :: Nat) a . a -> Vec a n -> Vec a (n+1)

data Queue :: * -> Num -> * where
  Q :: forall elem . pi (a b c :: Nat) . Vec elem a -> Vec elem b -> Queue elem (c + 3*a + b)

initQueue = Q {0} {0} {0} Nil Nil

enqueue :: forall elem (paid :: Nat) . elem -> Queue elem paid -> Queue elem (paid + 4)
enqueue x (Q {a} {b} {c} sA sB) = Q {a+1} {b} {c+1} (Cons x sA) sB

reverseS :: forall elem (paid :: Nat) . Queue elem paid -> Queue elem paid
reverseS (Q {0}   {b} {c} Nil         sB) = Q {0} {b} {c} Nil sB
reverseS (Q {a+1} {b} {c} (Cons x sA) sB) = reverseS (Q {a} {b+1} {c+2} sA (Cons x sB))

dequeue :: forall elem (paid :: Nat) . Queue elem paid -> Pair elem (Queue elem paid)
dequeue (Q {a} {b+1} {c} sA (Cons x sB)) = Pair x (Q {a} {b} {c+1} sA sB)
dequeue (Q {a+1} {0} {c} sA Nil)         = dequeue (reverseS (Q {a+1} {0} {c} sA Nil))



data Queue2 :: * -> Num -> * where
  Q2 :: forall elem (a b c :: Nat) . Vec elem a -> Vec elem b -> Queue2 elem (c + 3*a + b)


initQueue2 :: forall elem . Queue2 elem 0
initQueue2 = Q2 Nil Nil

enqueue2 :: forall elem (paid :: Nat) . elem -> Queue2 elem paid -> Queue2 elem (paid + 4)
enqueue2 x (Q2 sA sB) = Q2 (Cons x sA) sB

reverseS2 :: forall elem (paid :: Nat) . Queue2 elem paid -> Queue2 elem paid
reverseS2 (Q2 Nil         sB) = Q2 Nil sB
reverseS2 (Q2 (Cons x sA) sB) = reverseS2 (Q2 sA (Cons x sB))

dequeue2 :: forall elem (paid :: Nat) . Queue2 elem paid -> Pair elem (Queue2 elem paid)
dequeue2 (Q2 sA (Cons x sB)) = Pair x (Q2 sA sB)
dequeue2 (Q2 sA Nil)         = dequeue2 (reverseS2 (Q2 sA Nil))