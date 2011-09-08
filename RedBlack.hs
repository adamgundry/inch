{-# OPTIONS_GHC -F -pgmF ./toy #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables, NPlusKPatterns #-}

module RedBlack where


data Ex :: (Num -> *) -> * where
  Ex :: forall (p :: Num -> *)(n :: Num) . p n -> Ex p

unEx :: forall a (p :: Num -> *) . (forall (n :: Num) . p n -> a) -> Ex p -> a
unEx f (Ex x) = f x



data Colour :: Num -> * where
  Black  :: Colour 0
  Red    :: Colour 1

data Tree :: * -> Num -> Num -> * where
  E   :: forall a . Tree a 0 0
  TR  :: forall a (n :: Num) .
             a -> Tree a 0 n -> Tree a 0 n -> Tree a 1 n
  TB  :: forall a (cl cr n :: Num) .
             a -> Tree a cl n -> Tree a cr n -> Tree a 0 (n+1)

member :: forall a (cl n :: Num) .
              (a -> a -> Ordering) -> a -> Tree a cl n -> Bool
member cmp x E = False
member cmp x (TR y a b) = 
  let
    case_ LT = member cmp x a
    case_ EQ = True
    case_ GT = member cmp x b
  in case_ (cmp x y)
member cmp x (TB y a b) = 
  let
    case_ LT = member cmp x a
    case_ EQ = True
    case_ GT = member cmp x b
  in case_ (cmp x y)

blackHeight :: forall a b (c n :: Num) . b -> (b -> b) -> Tree a c n -> b
blackHeight zero suc E = zero
blackHeight zero suc (TB _ l _) = suc (blackHeight zero suc l)
blackHeight zero suc (TR _ l _) = blackHeight zero suc l


-- indexed by root colour, root black height, hole colour and hole black height

data TreeZip :: * -> Num -> Num -> Num -> Num -> * where
  Root  :: forall a (c n :: Num) . TreeZip a c n c n
  ZRL   :: forall a (n rc rn :: Num) .
               a -> TreeZip a rc rn 1 n -> Tree a 0 n -> TreeZip a rc rn 0 n
  ZRR   :: forall a (n rc rn :: Num) .
               a -> Tree a 0 n -> TreeZip a rc rn 1 n -> TreeZip a rc rn 0 n
  ZBL   :: forall a (n c rc rn hc :: Num) .
               a -> TreeZip a rc rn 0 (n+1) -> Tree a c n -> TreeZip a rc rn hc n
  ZBR   :: forall a (n c rc rn hc :: Num) .
               a -> Tree a c n -> TreeZip a rc rn 0 (n+1) -> TreeZip a rc rn hc n


plug :: forall a (rc rn c n :: Num) . Tree a c n -> TreeZip a rc rn c n -> Tree a rc rn
plug t Root         = t
plug t (ZRL x z r)  = plug (TR x t r) z
plug t (ZRR x l z)  = plug (TR x l t) z
plug t (ZBL x z r)  = plug (TB x t r) z
plug t (ZBR x l z)  = plug (TB x l t) z

plugBR :: forall a (n rn :: Num) . Tree a 0 n -> TreeZip a 0 rn 1 n -> Tree a 0 rn
plugBR t (ZBL x z r) = plug t (ZBL x z r)
plugBR t (ZBR x l z) = plug t (ZBR x l z)


-- insert :: forall a  p (n :: Num) .
--            a -> Tree a 0 n -> (forall (k :: Nat) . k <= 1 => Tree a 0 (n+k) -> p) -> p



data ColTree :: * -> Num -> * where
  CT :: forall a (c n :: Num) . Colour c -> Tree a c n -> ColTree a n



data InsProb :: * -> Num -> Num -> * where
  Level    :: forall a (c ci n :: Num) . Colour ci -> Tree a ci n -> InsProb a c n
  PanicRB  :: forall a (n :: Num) . a -> Tree a 1 n -> Tree a 0 n -> InsProb a 1 n
  PanicBR  :: forall a (n :: Num) . a -> Tree a 0 n -> Tree a 1 n -> InsProb a 1 n

solveIns :: forall a (c n rc rn :: Num) . 
             InsProb a c n -> TreeZip a rc rn c n -> ColTree a rn
solveIns (Level c t)      Root           = CT c t

solveIns (Level Red t)    (ZRL x z r)  = solveIns (PanicRB x t r) z
solveIns (Level Red t)    (ZRR x l z)  = solveIns (PanicBR x l t) z
solveIns (Level Black t)  (ZRL x z r)  = solveIns (Level Red (TR x t r)) z
solveIns (Level Black t)  (ZRR x l z)  = solveIns (Level Red (TR x l t)) z
solveIns (Level col t)    (ZBL x z r)  = solveIns (Level Black (TB x t r)) z
solveIns (Level col t)    (ZBR x l z)  = solveIns (Level Black (TB x l t)) z

solveIns (PanicRB xi (TR xil lil ril) ri)  (ZBL x z r)  =
    solveIns (Level Red (TR xi (TB xil lil ril) (TB x ri r))) z
solveIns (PanicBR xi li (TR xir lir rir))  (ZBL x z r)  =
    solveIns (Level Red (TR xir (TB xi li lir) (TB x rir r))) z


solveIns (PanicRB xi (TR xil lil ril) ri)  (ZBR x l z)  =
    solveIns (Level Red (TR xil (TB x l lil) (TB xi ril ri))) z
solveIns (PanicBR xi li (TR xir lir rir))  (ZBR x l z)  =
    solveIns (Level Red (TR xi (TB x l li) (TB xir lir rir))) z


ins :: forall a (c n rc rn :: Num) .
            (a -> a -> Ordering) -> a -> Tree a c n -> TreeZip a rc rn c n ->
            ColTree a rn
ins cmp x E           z = solveIns (Level Red (TR x E E)) z
ins cmp x (TR y l r)  z =
  let
     case_ LT = ins cmp x l (ZRL y z r)
     case_ _  = ins cmp x r (ZRR y l z)
  in case_ (cmp x y)
ins cmp x (TB y l r)  z =
  let
     case_ LT = ins cmp x l (ZBL y z r)
     case_ _  = ins cmp x r (ZBR y l z)
  in case_ (cmp x y)



r2b :: forall a (n :: Num) . Tree a 1 n -> Tree a 0 (n+1)
r2b (TR l x r) = TB l x r

unCT :: forall a (n :: Num) . ColTree a n -> Ex (Tree a 0)
unCT (CT Black t)  = Ex t
unCT (CT Red t)    = Ex (r2b t)


insert :: forall a (n :: Num) . (a -> a -> Ordering) -> a -> Tree a 0 n -> Ex (Tree a 0)
insert cmp x t = unCT (ins cmp x t Root)




solveDel :: forall a (rn n :: Num) . Tree a 0 n -> TreeZip a 0 rn 0 (n+1) ->
                Ex (Tree a 0)
solveDel t Root = Ex t

solveDel t (ZRL x z (TB y (TR lx ll lr) r)) = Ex (plug (TR lx (TB x t ll) (TB y lr r)) z)
solveDel t (ZRL x z (TB y l (TR rx rl rr))) = Ex (plug (TR y (TB x t l) (TB rx rl rr)) z)

-- Arrgh: these are one line in Agda because we can pattern match on the colours being black
solveDel t (ZRL x z (TB y E E))              = Ex (plugBR (TB x t (TR y E E)) z)
solveDel t (ZRL x z (TB y (TB lx ll lr) E))  = Ex (plugBR (TB x t (TR y (TB lx ll lr) E)) z)
solveDel t (ZRL x z (TB y E (TB rx rl rr)))  = Ex (plugBR (TB x t (TR y E (TB rx rl rr))) z)
solveDel t (ZRL x z (TB y (TB lx ll lr) (TB rx rl rr)))  = Ex (plugBR (TB x t (TR y (TB lx ll lr) (TB rx rl rr))) z)


solveDel t (ZRR x (TB y (TR lx ll lr) r) z)  = Ex (plug (TR y (TB lx ll lr) (TB x r t)) z)
solveDel t (ZRR x (TB y l (TR rx rl rr)) z)  = Ex (plug (TR rx (TB y l rl) (TB x rr t)) z)

-- Arrgh
solveDel t (ZRR x (TB y E E) z)              = Ex (plugBR (TB y E (TR x E t)) z)
solveDel t (ZRR x (TB y (TB lx ll lr) E) z)  = Ex (plugBR (TB y (TB lx ll lr) (TR x E t)) z)
solveDel t (ZRR x (TB y E (TB rx rl rr)) z)  = Ex (plugBR (TB y E (TR x (TB rx rl rr) t)) z)
solveDel t (ZRR x (TB y (TB lx ll lr) (TB rx rl rr)) z)  = Ex (plugBR (TB y (TB lx ll lr) (TR x (TB rx rl rr) t)) z)


-- Arrgh
solveDel t (ZBL x z (TR y (TB lx E lr) r))  = Ex (plug (TB y (TB lx (TR x t E) lr) r) z)
solveDel t (ZBL x z (TR y (TB lx (TB llx lll llr) lr) r))  = Ex (plug (TB y (TB lx (TR x t (TB llx lll llr)) lr) r) z)

solveDel t (ZBL x z (TR y (TB lx (TR llx lll llr) lr) r))  = Ex (plug (TB llx (TB x t lll) (TR y (TB lx llr lr) r)) z)

-- Arrgh
solveDel t (ZBL x z (TB y E r)) = solveDel (TB y (TR x t E) r) z
solveDel t (ZBL x z (TB y (TB lx ll lr) r))  = solveDel (TB y (TR x t (TB lx ll lr)) r) z

-- Arrgh
solveDel t (ZBL x z (TB y (TR lx ll lr) E))  = solveDel (TB lx (TR x t ll) (TR y lr E)) z
solveDel t (ZBL x z (TB y (TR lx ll lr) (TB rx rl rr)))  = solveDel (TB lx (TR x t ll) (TR y lr (TB rx rl rr))) z

solveDel t (ZBL x z (TB y (TR lx ll lr) (TR rx rl rr))) = Ex (plug (TB lx (TB x t ll) (TB y lr (TR rx rl rr))) z)


-- Arrgh
solveDel t (ZBR x (TR y l (TB rx rl E)) z) = Ex (plug (TB y l (TB rx rl (TR x E t))) z)
solveDel t (ZBR x (TR y l (TB rx rl (TB rrx rrl rrr))) z)  = Ex (plug (TB y l (TB rx rl (TR x (TB rrx rrl rrr) t))) z)

solveDel t (ZBR x (TR y l (TB rx rl (TR rrx rrl rrr))) z)  = Ex (plug (TB rrx (TR y l (TB rx rl rrl)) (TB x rrr t)) z)

-- Arrgh
solveDel t (ZBR x (TB y l E) z)  = solveDel (TB y l (TR x E t)) z
solveDel t (ZBR x (TB y l (TB lx ll lr)) z)  = solveDel (TB y l (TR x (TB lx ll lr) t)) z

-- Arrgh
solveDel t (ZBR x (TB y E (TR rx rl rr)) z)  = solveDel (TB rx (TR y E rl) (TR x rr t)) z
solveDel t (ZBR x (TB y (TB lx ll lr) (TR rx rl rr)) z)  = solveDel (TB rx (TR y (TB lx ll lr) rl) (TR x rr t)) z

solveDel t (ZBR x (TB y (TR lx ll lr) (TR rx rl rr)) z) = Ex (plug (TB y (TB lx ll lr) (TB rx rl (TR x rr t))) z)




findMin :: forall a (rn c :: Num) . pi (n :: Nat) . Tree a c (n+1) ->
               (a -> TreeZip a 0 rn c (n+1)) -> Ex (Tree a 0)

findMin {0}  (TR x (TB {-cr = blk-} y E E) r)              f = solveDel E (ZRL x (f y) r)

findMin {0}  (TR x (TB {-cr = red-} y E (TR lx ll lr)) r)  f = Ex (plug (TB lx ll lr) (ZRL x (f y) r))

findMin {0}  (TR x (TB y (TR k E E) lr) r)        f = Ex (plug E (ZBL y (ZRL x (f k) r) lr))
findMin {0}  (TB x (TR y E E) r)                  f = Ex (plug E (ZBL x (f y) r))

findMin {0}  (TB {-cr = red-} x E (TR lx ll lr))  f = Ex (plug (TB lx ll lr) (f x))

-- Arrgh
findMin {0}  (TB {-cr = blk-} x E E)              f = solveDel E (f x)

findMin {n+1} (TR x (TB y ll lr) r)               f = findMin {n} ll (\ k -> ZBL y (ZRL x (f k) r) lr)
findMin {n+1} (TB x l r)                          f = findMin {n} l  (\ k -> ZBL x (f k) r)



delFocus :: forall a (c rn :: Num) . pi (n :: Nat) . Tree a c n ->
                TreeZip a 0 rn c n -> Ex (Tree a 0)
delFocus {-red-} {0}    (TR x E E)                    z = Ex (plugBR E z)
delFocus {-red-} {n+1}  (TR x l r)                    z = findMin {n} r (\ k -> ZRR k l z)
delFocus {-blk-} {0}    E                             z = Ex (plug E z)
delFocus {-blk-} {1}    (TB x E E)                    z = solveDel E z
delFocus {-blk-} {1}    (TB x (TR y E E) E)           z = Ex (plug (TB y E E) z)
delFocus {-blk-} {1}    (TB x E (TR y E E))           z = Ex (plug (TB y E E) z)
delFocus {-blk-} {1}    (TB x (TR k E E) (TR y E E))  z = Ex (plug (TB k E (TR y E E)) z)
delFocus {-blk-} {n+2}  (TB x l r)                    z = findMin {n} r (\ k -> ZBR k l z)


del :: forall a (rn c :: Num) . (a -> a -> Ordering) -> a ->
           (pi (n :: Nat) . Tree a c n -> TreeZip a 0 rn c n -> Ex (Tree a 0))
del cmp x {n} E z = Ex (plug E z)
del cmp x {n} (TR y l r) z = 
  let
     case_ EQ = delFocus {n} (TR x l r) z
     case_ LT = del cmp x {n} l (ZRL y z r)
     case_ GT = del cmp x {n} r (ZRR y l z)
  in case_ (cmp x y)
del cmp x {n+1} (TB y l r) z =
  let
    case_ EQ = delFocus {n+1} (TB x l r) z
    case_ LT = del cmp x {n} l (ZBL y z r)
    case_ GT = del cmp x {n} r (ZBR y l z)
  in case_ (cmp x y)

delete :: forall a (n :: Num) . (a -> a -> Ordering) -> a ->
              (pi (n :: Nat) . Tree a 0 n -> Ex (Tree a 0))
delete cmp x {n} t = del cmp x {n} t Root



data RBT :: * -> * where
  RBT :: forall a . pi (n :: Nat) . Tree a 0 n -> RBT a

emptyRBT = RBT {0} E

ctToRBT :: forall a . pi (n :: Nat) . ColTree a n -> RBT a
ctToRBT {n} (CT Black t) = RBT {n} t
ctToRBT {n} (CT Red t)   = RBT {n+1} (r2b t)

insertRBT cmp x (RBT {n} t) = ctToRBT {n} (ins cmp x t Root)
deleteRBT cmp x (RBT {n} t) = delete cmp x {n} t
