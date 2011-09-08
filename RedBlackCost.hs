{-# OPTIONS_GHC -F -pgmF ./toy #-}

{-# LANGUAGE GADTs, RankNTypes, KindSignatures, ScopedTypeVariables, NPlusKPatterns #-}

module RedBlackCost where

-- Abstraction barrier

data Cost :: Num -> * -> * where
  Hide :: forall (n :: Nat) a . a -> Cost n a

force :: forall (n :: Nat) a . Cost n a -> a
force (Hide a) = a

returnW :: forall (n :: Nat) a . a -> Cost n a
returnW = Hide

bind :: forall (m n :: Nat) a b . Cost m a ->
            (a -> Cost n b) -> Cost (m+n) b
bind (Hide x) f = Hide (force (f x))

weaken :: forall (n :: Nat) a . pi (m :: Nat) . Cost n a -> Cost (m + n) a
weaken {m} (Hide a) = Hide a

magicweak :: forall (m n :: Nat) a . m <= n => Cost m a -> Cost n a
magicweak (Hide a) = Hide a

-- End of abstraction barrier


ret :: forall a . a -> Cost 0 a
ret = returnW

return1 :: forall a . a -> Cost 1 a
return1 = returnW

join :: forall (m n :: Nat) a . Cost m (Cost n a) -> Cost (m + n) a
join m = bind m id

tick :: forall (n :: Nat) a . Cost n a -> Cost (n + 1) a
tick = weaken {1}

fmp :: forall (n :: Nat) a b . (a -> b) -> Cost n a -> Cost n b
fmp f x = bind x (\ x -> ret (f x))




data Colour :: Num -> * where
  Black  :: Colour 0
  Red    :: Colour 1

data Tree :: * -> Num -> Num -> * where
  E   :: forall a . Tree a 0 0
  TR  :: forall a (n :: Nat) .
             a -> Tree a 0 n -> Tree a 0 n -> Tree a 1 n
  TB  :: forall a (cl cr n :: Nat) .
             a -> Tree a cl n -> Tree a cr n -> Tree a 0 (n+1)


data RBT :: * -> * where
  RBT :: forall a (n :: Nat) . Tree a 0 n -> RBT a

empty = RBT E


data TreeZip :: * -> Num -> Num -> Num -> Num -> Num -> * where
  Root  :: forall a (c n :: Nat) . TreeZip a c n c n 0
  ZRL   :: forall a (n rc rn d :: Nat) .
               a -> TreeZip a rc rn 1 n d -> Tree a 0 n -> TreeZip a rc rn 0 n (d + 1)
  ZRR   :: forall a (n rc rn d :: Nat) .
               a -> Tree a 0 n -> TreeZip a rc rn 1 n d -> TreeZip a rc rn 0 n (d + 1)
  ZBL   :: forall a (n c rc rn hc d :: Nat) .
               a -> TreeZip a rc rn 0 (n+1) d -> Tree a c n -> TreeZip a rc rn hc n (d + 1)
  ZBR   :: forall a (n c rc rn hc d :: Nat) .
               a -> Tree a c n -> TreeZip a rc rn 0 (n+1) d -> TreeZip a rc rn hc n (d + 1)


plug ::  forall a (rc rn c n d :: Num) . Tree a c n -> TreeZip a rc rn c n d ->
            Cost (d + 1) (Tree a rc rn)
plug t Root         = tick (ret t)
plug t (ZRL x z r)  = tick (plug (TR x t r) z)
plug t (ZRR x l z)  = tick (plug (TR x l t) z)
plug t (ZBL x z r)  = tick (plug (TB x t r) z)
plug t (ZBR x l z)  = tick (plug (TB x l t) z)

plugBR :: forall a (n rn d :: Num) . Tree a 0 n -> TreeZip a 0 rn 1 n d -> Cost (d + 1) (Tree a 0 rn)
plugBR t (ZBL x z r) = plug t (ZBL x z r)
plugBR t (ZBR x l z) = plug t (ZBR x l z)


search :: forall a p (rn :: Nat) . (a -> a -> Ordering) ->
              (forall (d :: Nat) . d <= (2 * rn) => TreeZip a 0 rn 0 0 d -> p) ->
              (forall (c n d :: Nat) . ((2 * n) + d) <= (2 * rn) =>
                  TreeZip a 0 rn c n d -> Tree a c n -> p) ->
              a -> Tree a 0 rn -> Cost (2 * rn + 1) p
search cmp fe fn x = 
  let
    help :: forall (n c d :: Nat) . (1 + (2 * n) + d) <= (2 * rn) =>
                TreeZip a 0 rn c n d -> Tree a c n -> Cost (2 + 2 * n) p
    help z E          = tick (returnW (fe z))
    help z (TR y l r) = tick (let case_ EQ = returnW (fn z (TR y l r))
                                  case_ LT = helpB (ZRL y z r) l
                                  case_ GT = helpB (ZRR y l z) r
                              in case_ (cmp x y))
    help z (TB y l r) = tick (let case_ EQ = returnW (fn z (TB y l r))
                                  case_ LT = weaken {1} (help (ZBL y z r) l)
                                  case_ GT = weaken {1} (help (ZBR y l z) r)
                              in case_ (cmp x y))

    helpB :: forall (n d :: Nat) . ((2 * n) + d) <= (2 * rn) =>
                TreeZip a 0 rn 0 n d -> Tree a 0 n -> Cost (1 + 2 * n) p
    helpB z E          = tick (returnW (fe z))
    helpB z (TB y l r) = tick (let case_ EQ = returnW (fn z (TB y l r))
                                   case_ LT = help (ZBL y z r) l
                                   case_ GT = help (ZBR y l z) r
                               in case_ (cmp x y))

  in helpB Root

member cmp x t = force (search cmp (\ z -> False) (\ z zz -> True) x t)





data ColTree :: * -> Num -> * where
  CT :: forall a (c n :: Nat) . Colour c -> Tree a c n -> ColTree a n



data InsProb :: * -> Num -> Num -> * where
  Level    :: forall a (c ci n :: Nat) . Colour ci -> Tree a ci n -> InsProb a c n
  PanicRB  :: forall a (n :: Nat) . a -> Tree a 1 n -> Tree a 0 n -> InsProb a 1 n
  PanicBR  :: forall a (n :: Nat) . a -> Tree a 0 n -> Tree a 1 n -> InsProb a 1 n

solveIns :: forall a (c n rc rn d :: Nat) . 
             InsProb a c n -> TreeZip a rc rn c n d -> Cost (d + 1) (ColTree a rn)
solveIns (Level c t)      Root         = tick (ret (CT c t))

solveIns (Level Red t)    (ZRL x z r)  = tick (solveIns (PanicRB x t r) z)
solveIns (Level Red t)    (ZRR x l z)  = tick (solveIns (PanicBR x l t) z)
solveIns (Level Black t)  (ZRL x z r)  = tick (solveIns (Level Red (TR x t r)) z)
solveIns (Level Black t)  (ZRR x l z)  = tick (solveIns (Level Red (TR x l t)) z)
solveIns (Level col t)    (ZBL x z r)  = tick (solveIns (Level Black (TB x t r)) z)
solveIns (Level col t)    (ZBR x l z)  = tick (solveIns (Level Black (TB x l t)) z)

solveIns (PanicRB xi (TR xil lil ril) ri)  (ZBL x z r)  =
    tick (solveIns (Level Red (TR xi (TB xil lil ril) (TB x ri r))) z)
solveIns (PanicBR xi li (TR xir lir rir))  (ZBL x z r)  =
    tick (solveIns (Level Red (TR xir (TB xi li lir) (TB x rir r))) z)


solveIns (PanicRB xi (TR xil lil ril) ri)  (ZBR x l z)  =
    tick (solveIns (Level Red (TR xil (TB x l lil) (TB xi ril ri))) z)
solveIns (PanicBR xi li (TR xir lir rir))  (ZBR x l z)  =
    tick (solveIns (Level Red (TR xi (TB x l li) (TB xir lir rir))) z)


{-
ins :: forall a (n :: Nat) . (a -> a -> Ordering) -> a -> Tree a 0 n ->
           Cost (4 * n + 5) (ColTree a n)
ins cmp x t =
  let
    f :: forall (x :: Nat) . x <= (2 * n) => TreeZip a 0 n 0 0 x ->
             Cost (2 * n + 2) (ColTree a n)
    f z = undefined -- tick (magicweak (solveIns (Level Red (TR x E E)) z))
  in tick (join (search cmp
    f
    (\ z zz -> tick (returnW (CT Black t)))
    x
    t))

-}


data SearchResult :: * -> Num -> * where
  Nope  :: forall a (rn d :: Nat) . d <= (2 * rn) =>
               TreeZip a 0 rn 0 0 d -> SearchResult a rn
  Yep   :: forall a (rn c n d :: Nat) . ((2 * n) + d) <= (2 * rn) =>
               TreeZip a 0 rn c n d -> Tree a c n -> SearchResult a rn

search2 cmp x = search cmp Nope Yep x


ins :: forall a (n :: Nat) . (a -> a -> Ordering) -> a -> Tree a 0 n ->
           Cost (4 * n + 5) (ColTree a n)
ins cmp x t = 
  let 
    f :: SearchResult a n -> Cost (2 * n + 3) (ColTree a n)
    f (Nope z)   = tick (magicweak (solveIns (Level Red (TR x E E)) z))
    f (Yep _ _)  = tick (returnW (CT Black t))
  in tick (bind (search2 cmp x t) f)




r2b :: forall a (n :: Num) . Tree a 1 n -> Tree a 0 (n+1)
r2b (TR l x r) = TB l x r

unCT :: forall a (n :: Num) . ColTree a n -> RBT a
unCT (CT Black t)  = RBT t
unCT (CT Red t)    = RBT (r2b t)


insert cmp x (RBT t) = unCT (force (ins cmp x t))







solveDel :: forall a (rn n d :: Nat) . Tree a 0 n -> TreeZip a 0 rn 0 (n+1) d ->
                Cost (d + 1) (RBT a)
solveDel t Root = tick (returnW (RBT t))

solveDel t (ZRL x z (TB y (TR lx ll lr) r)) = tick (fmp RBT (plug (TR lx (TB x t ll) (TB y lr r)) z))
solveDel t (ZRL x z (TB y l (TR rx rl rr))) = tick (fmp RBT (plug (TR y (TB x t l) (TB rx rl rr)) z))

-- Arrgh: these are one line in Agda because we can pattern match on the colours being black
solveDel t (ZRL x z (TB y E E))              = tick (fmp RBT (plugBR (TB x t (TR y E E)) z))
solveDel t (ZRL x z (TB y (TB lx ll lr) E))  = tick (fmp RBT (plugBR (TB x t (TR y (TB lx ll lr) E)) z))
solveDel t (ZRL x z (TB y E (TB rx rl rr)))  = tick (fmp RBT (plugBR (TB x t (TR y E (TB rx rl rr))) z))
solveDel t (ZRL x z (TB y (TB lx ll lr) (TB rx rl rr)))  = tick (fmp RBT (plugBR (TB x t (TR y (TB lx ll lr) (TB rx rl rr))) z))


solveDel t (ZRR x (TB y (TR lx ll lr) r) z)  = tick (fmp RBT (plug (TR y (TB lx ll lr) (TB x r t)) z))
solveDel t (ZRR x (TB y l (TR rx rl rr)) z)  = tick (fmp RBT (plug (TR rx (TB y l rl) (TB x rr t)) z))

-- Arrgh
solveDel t (ZRR x (TB y E E) z)              = tick (fmp RBT (plugBR (TB y E (TR x E t)) z))
solveDel t (ZRR x (TB y (TB lx ll lr) E) z)  = tick (fmp RBT (plugBR (TB y (TB lx ll lr) (TR x E t)) z))
solveDel t (ZRR x (TB y E (TB rx rl rr)) z)  = tick (fmp RBT (plugBR (TB y E (TR x (TB rx rl rr) t)) z))
solveDel t (ZRR x (TB y (TB lx ll lr) (TB rx rl rr)) z)  = tick (fmp RBT (plugBR (TB y (TB lx ll lr) (TR x (TB rx rl rr) t)) z))


-- Arrgh
solveDel t (ZBL x z (TR y (TB lx E lr) r))  = tick (fmp RBT (plug (TB y (TB lx (TR x t E) lr) r) z))
solveDel t (ZBL x z (TR y (TB lx (TB llx lll llr) lr) r))  = tick (fmp RBT (plug (TB y (TB lx (TR x t (TB llx lll llr)) lr) r) z))

solveDel t (ZBL x z (TR y (TB lx (TR llx lll llr) lr) r))  = tick (fmp RBT (plug (TB llx (TB x t lll) (TR y (TB lx llr lr) r)) z))

-- Arrgh
solveDel t (ZBL x z (TB y E r)) = tick (solveDel (TB y (TR x t E) r) z)
solveDel t (ZBL x z (TB y (TB lx ll lr) r))  = tick (solveDel (TB y (TR x t (TB lx ll lr)) r) z)

-- Arrgh
solveDel t (ZBL x z (TB y (TR lx ll lr) E))  = tick (solveDel (TB lx (TR x t ll) (TR y lr E)) z)
solveDel t (ZBL x z (TB y (TR lx ll lr) (TB rx rl rr)))  = tick (solveDel (TB lx (TR x t ll) (TR y lr (TB rx rl rr))) z)

solveDel t (ZBL x z (TB y (TR lx ll lr) (TR rx rl rr))) = tick (fmp RBT (plug (TB lx (TB x t ll) (TB y lr (TR rx rl rr))) z))


-- Arrgh
solveDel t (ZBR x (TR y l (TB rx rl E)) z) = tick (fmp RBT (plug (TB y l (TB rx rl (TR x E t))) z))
solveDel t (ZBR x (TR y l (TB rx rl (TB rrx rrl rrr))) z)  = tick (fmp RBT (plug (TB y l (TB rx rl (TR x (TB rrx rrl rrr) t))) z))

solveDel t (ZBR x (TR y l (TB rx rl (TR rrx rrl rrr))) z)  = tick (fmp RBT (plug (TB rrx (TR y l (TB rx rl rrl)) (TB x rrr t)) z))

-- Arrgh
solveDel t (ZBR x (TB y l E) z)  = tick (solveDel (TB y l (TR x E t)) z)
solveDel t (ZBR x (TB y l (TB lx ll lr)) z)  = tick (solveDel (TB y l (TR x (TB lx ll lr) t)) z)

-- Arrgh
solveDel t (ZBR x (TB y E (TR rx rl rr)) z)  = tick (solveDel (TB rx (TR y E rl) (TR x rr t)) z)
solveDel t (ZBR x (TB y (TB lx ll lr) (TR rx rl rr)) z)  = tick (solveDel (TB rx (TR y (TB lx ll lr) rl) (TR x rr t)) z)

solveDel t (ZBR x (TB y (TR lx ll lr) (TR rx rl rr)) z) = tick (fmp RBT (plug (TB y (TB lx ll lr) (TB rx rl (TR x rr t))) z))


findMin :: forall a (rn c d n :: Nat) . Tree a c (n+1) ->
               (a -> TreeZip a 0 rn c (n+1) d) ->
                   Cost (3 * n + d + 4) (RBT a)
findMin (TR x (TB y E E) r)                 f = tick (magicweak (solveDel E (ZRL x (f y) r)))
findMin (TR x (TB y E (TR lx ll lr)) r)     f = tick (magicweak (fmp RBT (plug (TB lx ll lr) (ZRL x (f y) r))))

findMin (TR x (TB y (TR k E E) lr) r)       f = tick (magicweak (fmp RBT (plug E (ZBL y (ZRL x (f k) r) lr))))

findMin (TB x (TR y E E) r)                 f = tick (magicweak (fmp RBT (plug E (ZBL x (f y) r))))
findMin (TB x E (TR lx ll lr))              f = tick (magicweak (fmp RBT (plug (TB lx ll lr) (f x))))
findMin (TB x E E)                          f = tick (magicweak (solveDel E (f x)))

findMin (TR x (TB y (TB llx lll llr) lr) r) f = tick (findMin (TB llx lll llr) (\ k -> ZBL y (ZRL x (f k) r) lr))
findMin (TB x (TB lx ll lr) r)              f = tick (weaken {1} (findMin (TB lx ll lr)  (\ k -> ZBL x (f k) r)))




delFocus :: forall a (c rn d n :: Nat) . Tree a c n -> TreeZip a 0 rn c n d ->
                Cost (3 * n + d + 3) (RBT a)
delFocus (TR _ E          E)              z = tick (weaken {1} (fmp RBT (plugBR E z)))
delFocus (TR _ l          (TB rx rl rr))  z = tick (findMin (TB rx rl rr) (\ k -> ZRR k l z))
delFocus E                                z = tick (magicweak (fmp RBT (plug E z)))
delFocus (TB _ E          E)              z = tick (magicweak (solveDel E z))
delFocus (TB _ (TR y E E) E)              z = tick (magicweak (fmp RBT (plug (TB y E E) z)))
delFocus (TB _ E          (TR y E E))     z = tick (magicweak (fmp RBT (plug (TB y E E) z)))
delFocus (TB _ (TR k E E) (TR y E E))     z = tick (magicweak (fmp RBT (plug (TB k E (TR y E E)) z)))
delFocus (TB _ l          (TB rx rl rr))  z = tick (weaken {3} (findMin (TB rx rl rr) (\ k -> ZBR k l z)))
delFocus (TB _ (TB lx ll lr)  r)          z = tick (weaken {3} (findMin r (\ k -> ZBR k (TB lx ll lr) z)))






del :: forall a (n :: Nat) . (a -> a -> Ordering) -> a -> Tree a 0 n ->
           Cost (5 * n + 6) (RBT a)
del cmp x t = 
  let 
    f :: SearchResult a n -> Cost (3 * n + 4) (RBT a)
    f (Nope _)   = tick (returnW (RBT t))
    f (Yep z t)  = tick (magicweak (delFocus t z))
  in tick (bind (search2 cmp x t) f)

delete cmp x (RBT t) = force (del cmp x t)