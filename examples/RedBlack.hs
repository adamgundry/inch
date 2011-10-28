{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

{-
  An implementation of red-black tree insertion and deletion using an
  indexed zipper. The type indices guarantee that the ordering, colour
  and height invariants are preserved. 
-}

module RedBlack where

-- We can't (yet) lift types to kinds automatically, but we can
-- represent finite enumerations using numbers. Here we use 0 for
-- black and 1 for red, and use a singleton type to fake pi-types for
-- colours. Type synonyms would make this clearer... or proper lifting
-- of algebraic data types to kinds.

data Colour :: Integer -> * where
    Black  :: Colour 0
    Red    :: Colour 1
  deriving Show

data Tree :: Integer -> Integer -> Integer -> Nat -> * where
    E   ::  forall (lo hi :: Integer) . lo < hi => Tree lo hi 0 0
    TR  ::  forall (lo hi :: Integer)(n :: Nat) . pi (x :: Integer) .
                Tree lo x 0 n -> Tree x hi 0 n -> Tree lo hi 1 n
    TB  ::  forall (lo hi cl cr :: Integer)(n :: Nat) . pi (x :: Integer) .
                Tree lo x cl n -> Tree x hi cr n -> Tree lo hi 0 (n+1)
  deriving Show

data RBT :: Integer -> Integer -> * where
    RBT :: forall (lo hi :: Integer)(n :: Nat) . Tree lo hi 0 n -> RBT lo hi
  deriving Show

empty = RBT E

data TreeZip ::  Integer -> Integer -> Integer -> Nat ->
                 Integer -> Integer -> Integer -> Nat -> * where
    Root  :: forall (lo hi c :: Integer)(n :: Nat) . TreeZip lo hi c n lo hi c n
    ZRL   :: forall (rlo rhi lo hi rc :: Integer)(rn n :: Nat) . pi (x :: Integer) .
                 TreeZip rlo rhi rc rn lo hi 1 n -> Tree x hi 0 n ->
                     TreeZip rlo rhi rc rn lo x 0 n
    ZRR   :: forall (rlo rhi lo hi rc :: Integer)(rn n :: Nat) . pi (x :: Integer) .
                 Tree lo x 0 n -> TreeZip rlo rhi rc rn lo hi 1 n  ->
                     TreeZip rlo rhi rc rn x hi 0 n
    ZBL   :: forall (rlo rhi lo hi rc c hc :: Integer)(rn n  :: Nat) . pi (x :: Integer) . 
                 TreeZip rlo rhi rc rn lo hi 0 (n+1)  -> Tree x hi c n ->
                     TreeZip rlo rhi rc rn lo x hc n
    ZBR   :: forall (rlo rhi lo hi rc c hc :: Integer)(rn n  :: Nat) . pi (x :: Integer) .
                 Tree lo x c n -> TreeZip rlo rhi rc rn lo hi 0 (n+1) ->
                     TreeZip rlo rhi rc rn x hi hc n
  deriving Show

plug ::  forall (rlo rhi lo hi rc rn c n :: Integer) . Tree lo hi c n ->
             TreeZip rlo rhi rc rn lo hi c n -> Tree rlo rhi rc rn
plug t Root           = t
plug t (ZRL {x} z r)  = plug (TR {x} t r) z
plug t (ZRR {x} l z)  = plug (TR {x} l t) z
plug t (ZBL {x} z r)  = plug (TB {x} t r) z
plug t (ZBR {x} l z)  = plug (TB {x} l t) z

plugBR :: forall (rlo rhi lo hi n rn :: Integer) . Tree lo hi 0 n ->
              TreeZip rlo rhi 0 rn lo hi 1 n -> Tree rlo rhi 0 rn
plugBR t (ZBL {x} z r) = plug t (ZBL {x} z r)
plugBR t (ZBR {x} l z) = plug t (ZBR {x} l z)

data SearchResult :: Integer -> Integer -> Integer -> Integer -> * where
  Nope  ::  forall (x rlo rhi lo hi :: Integer)(rn :: Nat) . lo < x, x < hi =>
                TreeZip rlo rhi 0 rn lo hi 0 0 -> SearchResult x rlo rhi rn
  Yep   ::  forall (x rlo rhi lo hi c :: Integer)(rn n :: Nat) .
                TreeZip rlo rhi 0 rn lo hi c n -> Tree lo hi c n ->
                    SearchResult x rlo rhi rn

search ::  forall (rlo rhi :: Integer)(rn :: Nat) .
               pi (x :: Integer) . rlo < x, x < rhi =>
                    Tree rlo rhi 0 rn -> SearchResult x rlo rhi rn
search {x} = help Root
  where
    help ::  forall (lo hi c :: Integer)(n :: Nat) . lo < x, x < hi =>
                 TreeZip rlo rhi 0 rn lo hi c n -> Tree lo hi c n ->
                     SearchResult x rlo rhi rn
    help z E                       = Nope z
    help z (TR {y} l r) | {x < y}  = help (ZRL {y} z r) l
    help z (TR {y} l r) | {x ~ y}  = Yep z (TR {y} l r)
    help z (TR {y} l r) | {x > y}  = help (ZRR {y} l z) r
    help z (TB {y} l r) | {x < y}  = help (ZBL {y} z r) l
    help z (TB {y} l r) | {x ~ y}  = Yep z (TB {y} l r)
    help z (TB {y} l r) | {x > y}  = help (ZBR {y} l z) r

member ::  forall (lo hi :: Integer) . pi (x :: Integer) . lo < x, x < hi =>
               RBT lo hi -> Bool
member {x} (RBT t) = case search {x} t of
                       Nope _   -> False
                       Yep _ _  -> True


data InsProb :: Integer -> Integer -> Integer -> Integer -> * where
  Level    ::  forall (lo hi c ci :: Integer)( n :: Nat) .
                   Colour ci -> Tree lo hi ci n -> InsProb lo hi c n
  PanicRB  ::  forall (lo hi :: Integer)(n :: Nat) . pi (x :: Integer) .
                   Tree lo x 1 n -> Tree x hi 0 n -> InsProb lo hi 1 n
  PanicBR  ::  forall (lo hi :: Integer)(n :: Nat) . pi (x :: Integer) .
                   Tree lo x 0 n -> Tree x hi 1 n -> InsProb lo hi 1 n

solveIns ::  forall (rlo rhi lo hi c rc :: Integer)(rn n :: Nat) . 
                InsProb lo hi c n -> TreeZip rlo rhi rc rn lo hi c n ->
                    RBT rlo rhi
solveIns (Level c t)      Root           = rbt c t

solveIns (Level Red t)    (ZRL {x} z r)  = solveIns (PanicRB {x} t r) z
solveIns (Level Red t)    (ZRR {x} l z)  = solveIns (PanicBR {x} l t) z
solveIns (Level Black t)  (ZRL {x} z r)  = solveIns (Level Red (TR {x} t r)) z
solveIns (Level Black t)  (ZRR {x} l z)  = solveIns (Level Red (TR {x} l t)) z
solveIns (Level col t)    (ZBL {x} z r)  = solveIns (Level Black (TB {x} t r)) z
solveIns (Level col t)    (ZBR {x} l z)  = solveIns (Level Black (TB {x} l t)) z

solveIns (PanicRB {xi} (TR {xil} lil ril) ri)  (ZBL {x} z r)  =
    solveIns (Level Red (TR {xi} (TB {xil} lil ril) (TB {x} ri r))) z
solveIns (PanicBR {xi} li (TR {xir} lir rir))  (ZBL {x} z r)  =
    solveIns (Level Red (TR {xir} (TB {xi} li lir) (TB {x} rir r))) z

solveIns (PanicRB {xi} (TR {xil} lil ril) ri)  (ZBR {x} l z)  =
    solveIns (Level Red (TR {xil} (TB {x} l lil) (TB {xi} ril ri))) z
solveIns (PanicBR {xi} li (TR {xir} lir rir))  (ZBR {x} l z)  =
    solveIns (Level Red (TR {xi} (TB {x} l li) (TB {xir} lir rir))) z

insert ::  forall (lo hi :: Integer)(n :: Nat) . pi (x :: Integer) . lo < x, x < hi =>
               Tree lo hi 0 n -> RBT lo hi
insert {x} t = case search {x} t :: SearchResult x lo hi n of
    Nope z   -> solveIns (Level Red (TR {x} E E)) z
    Yep _ _  -> RBT t


r2b :: forall (lo hi n :: Integer) . Tree lo hi 1 n -> Tree lo hi 0 (n+1)
r2b (TR {x} l r) = TB {x} l r

rbt :: forall (lo hi c :: Integer)(n :: Nat) . Colour c -> Tree lo hi c n -> RBT lo hi
rbt Black  t = RBT t
rbt Red    t = RBT (r2b t)


solveDel ::  forall (rlo rhi lo hi :: Integer)(rn n :: Nat) . Tree lo hi 0 n ->
                 TreeZip rlo rhi 0 rn lo hi 0 (n+1) -> RBT rlo rhi
solveDel t Root = RBT t

solveDel t (ZRL {x} z (TB {y} (TR {lx} ll lr) r)) = RBT (plug (TR {lx} (TB {x} t ll) (TB {y} lr r)) z)
solveDel t (ZRL {x} z (TB {y} l (TR {rx} rl rr))) = RBT (plug (TR {y} (TB {x} t l) (TB {rx} rl rr)) z)

-- Arrgh: these are one line in Agda because we can pattern match on the colours being black
solveDel t (ZRL {x} z (TB {y} E E))              = RBT (plugBR (TB {x} t (TR {y} E E)) z)
solveDel t (ZRL {x} z (TB {y} (TB {lx} ll lr) (TB {rx} rl rr)))  = RBT (plugBR (TB {x} t (TR {y} (TB {lx} ll lr) (TB {rx} rl rr))) z)


solveDel t (ZRR {x} (TB {y} (TR {lx} ll lr) r) z)  = RBT (plug (TR {y} (TB {lx} ll lr) (TB {x} r t)) z)
solveDel t (ZRR {x} (TB {y} l (TR {rx} rl rr)) z)  = RBT (plug (TR {rx} (TB {y} l rl) (TB {x} rr t)) z)

-- Arrgh
solveDel t (ZRR {x} (TB {y} E E) z)              = RBT (plugBR (TB {y} E (TR {x} E t)) z)
solveDel t (ZRR {x} (TB {y} (TB {lx} ll lr) (TB {rx} rl rr)) z)  = RBT (plugBR (TB {y} (TB {lx} ll lr) (TR {x} (TB {rx} rl rr) t)) z)


-- Arrgh
solveDel t (ZBL {x} z (TR {y} (TB {lx} E lr) r))  = RBT (plug (TB {y} (TB {lx} (TR {x} t E) lr) r) z)
solveDel t (ZBL {x} z (TR {y} (TB {lx} (TB {llx} lll llr) lr) r))  = RBT (plug (TB {y} (TB {lx} (TR {x} t (TB {llx} lll llr)) lr) r) z)

solveDel t (ZBL {x} z (TR {y} (TB {lx} (TR {llx} lll llr) lr) r))  = RBT (plug (TB {llx} (TB {x} t lll) (TR {y} (TB {lx} llr lr) r)) z)

-- Arrgh
solveDel t (ZBL {x} z (TB {y} E r)) = solveDel (TB {y} (TR {x} t E) r) z
solveDel t (ZBL {x} z (TB {y} (TB {lx} ll lr) r))  = solveDel (TB {y} (TR {x} t (TB {lx} ll lr)) r) z

-- Arrgh
solveDel t (ZBL {x} z (TB {y} (TR {lx} ll lr) E))  = solveDel (TB {lx} (TR {x} t ll) (TR {y} lr E)) z
solveDel t (ZBL {x} z (TB {y} (TR {lx} ll lr) (TB {rx} rl rr)))  = solveDel (TB {lx} (TR {x} t ll) (TR {y} lr (TB {rx} rl rr))) z

solveDel t (ZBL {x} z (TB {y} (TR {lx} ll lr) (TR {rx} rl rr))) = RBT (plug (TB {lx} (TB {x} t ll) (TB {y} lr (TR {rx} rl rr))) z)


-- Arrgh
solveDel t (ZBR {x} (TR {y} l (TB {rx} rl E)) z) = RBT (plug (TB {y} l (TB {rx} rl (TR {x} E t))) z)
solveDel t (ZBR {x} (TR {y} l (TB {rx} rl (TB {rrx} rrl rrr))) z)  = RBT (plug (TB {y} l (TB {rx} rl (TR {x} (TB {rrx} rrl rrr) t))) z)

solveDel t (ZBR {x} (TR {y} l (TB {rx} rl (TR {rrx} rrl rrr))) z)  = RBT (plug (TB {rrx} (TR {y} l (TB {rx} rl rrl)) (TB {x} rrr t)) z)

-- Arrgh
solveDel t (ZBR {x} (TB {y} l E) z)  = solveDel (TB {y} l (TR {x} E t)) z
solveDel t (ZBR {x} (TB {y} l (TB {lx} ll lr)) z)  = solveDel (TB {y} l (TR {x} (TB {lx} ll lr) t)) z

-- Arrgh
solveDel t (ZBR {x} (TB {y} E (TR {rx} rl rr)) z)  = solveDel (TB {rx} (TR {y} E rl) (TR {x} rr t)) z
solveDel t (ZBR {x} (TB {y} (TB {lx} ll lr) (TR {rx} rl rr)) z)  = solveDel (TB {rx} (TR {y} (TB {lx} ll lr) rl) (TR {x} rr t)) z

solveDel t (ZBR {x} (TB {y} (TR {lx} ll lr) (TR {rx} rl rr)) z) = RBT (plug (TB {y} (TB {lx} ll lr) (TB {rx} rl (TR {x} rr t))) z)


findMin ::  forall (rlo rhi lo hi c :: Integer)(rn n :: Nat) . Tree lo hi c (n+1) ->
                (pi (k :: Integer) . lo < k => TreeZip rlo rhi 0 rn k hi c (n+1)) ->
                    RBT rlo rhi
findMin (TR {x} (TB {y} E E) r)                    f = solveDel E (ZRL {x} (f {y}) r)
findMin (TR {x} (TB {y} E (TR {lx} ll lr)) r)      f = RBT (plug (TB {lx} ll lr) (ZRL {x} (f {y}) r))

findMin (TR {x} (TB {y} (TR {k} E E) lr) r)        f = RBT (plug E (ZBL {y} (ZRL {x} (f {k}) r) lr))

findMin (TB {x} (TR {y} E E) r)                    f = RBT (plug E (ZBL {x} (f {y}) r))
findMin (TB {x} E (TR {lx} ll lr))                 f = RBT (plug (TB {lx} ll lr) (f {x}))
findMin (TB {x} E E)                               f = solveDel E (f {x})

findMin (TR {x} (TB {y} (TB {llx} lll llr) lr) r)  f = findMin (TB {llx} lll llr) (\ {k} -> ZBL {y} (ZRL {x} (f {k}) r) lr)
findMin (TB {x} (TB {lx} ll lr) r)                 f = findMin (TB {lx} ll lr)  (\ {k} -> ZBL {x} (f {k}) r)

wkTree ::  forall (lo hi ha c n :: Integer) . hi < ha => Tree lo hi c n -> Tree lo ha c n
wkTree E             = E
wkTree (TR {x} l r)  = TR {x} l (wkTree r)
wkTree (TB {x} l r)  = TB {x} l (wkTree r)

delFocus ::  forall (rlo rhi lo hi c :: Integer)(rn n :: Nat) . Tree lo hi c n ->
                 TreeZip rlo rhi 0 rn lo hi c n -> RBT rlo rhi
delFocus E                                   z = RBT (plug E z)
delFocus (TR {x} E E)                        z = RBT (plugBR E z)
delFocus (TR {x} l (TB {rx} rl rr))          z = findMin (TB {rx} rl rr) (\ {k} -> ZRR {k} (wkTree l) z)
delFocus (TB {x} E E)                        z = solveDel E z
delFocus (TB {x} (TR {y} E E) E)             z = RBT (plug (TB {y} E E) z)
delFocus (TB {x} E (TR {y} E E))             z = RBT (plug (TB {y} E E) z)
delFocus (TB {x} (TR {k} E E) (TR {y} E E))  z = RBT (plug (TB {k} E (TR {y} E E)) z)
delFocus (TB {x} l (TB {rx} rl rr))          z = findMin (TB {rx} rl rr) (\ {k} -> ZBR {k} (wkTree l) z)
delFocus (TB {x} (TB {lx} ll lr)  r)         z = findMin r (\ {k} -> ZBR {k} (wkTree (TB {lx} ll lr)) z)

 
delete ::  forall (lo hi :: Integer) . pi (x :: Integer) . lo < x, x < hi =>
               RBT lo hi -> RBT lo hi
delete {x} (RBT t) = f (search {x} t)
  where
    f :: forall (n :: Nat) . SearchResult x lo hi n -> RBT lo hi
    f (Nope _)   = RBT t
    f (Yep z t)  = delFocus t z



-- Suppose we want to hide the bounds from the user of our red-black
-- tree library. In a dependently typed language, we could add top and
-- bottom elements to the order, but we can't do so here for the
-- integers. Instead, here's a solution that weakens the bounds on the
-- tree as necessary. Note that wkTree2 could safely be implemented
-- using unsafeCoerce. 

data T where
    T :: forall (n :: Nat)(lo hi :: Num) . Tree lo hi 0 n -> T
  deriving Show

emptyT = T E

rbtToT :: forall (lo hi :: Num) . RBT lo hi -> T
rbtToT (RBT t) = T t

insertT :: pi (x :: Num) . T -> T
insertT {x} (T t) = rbtToT (insert {x} (weakling {x} t))

deleteT :: pi (x :: Num) . T -> T
deleteT {x} (T t) = rbtToT (delete {x} (RBT (weakling {x} t)))

weakling :: forall (lo hi c n :: Num) . pi (x :: Num) . Tree lo hi c n ->
              Tree (min lo (x-1)) (max hi (x+1)) c n
weakling {x} t = wkTree2 t

wkTree2 :: forall (lo lo' hi hi' c n :: Num) . lo' <= lo, hi <= hi' =>
               Tree lo hi c n -> Tree lo' hi' c n
wkTree2 E            = E
wkTree2 (TB {x} l r) = TB {x} (wkTree2 l) (wkTree2 r)
wkTree2 (TR {x} l r) = TR {x} (wkTree2 l) (wkTree2 r)