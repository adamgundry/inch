{-# OPTIONS_GHC -F -pgmF inch #-}
{-# LANGUAGE RankNTypes, GADTs, KindSignatures, ScopedTypeVariables,
             NPlusKPatterns #-}

{-
  An implementation of red-black tree insertion and deletion that uses
  Nils Anders Danielsson's technique for semiformal time complexity
  analysis to show that these operations are linear in black
  height. See the RedBlack module for an implementation of the tree
  operations without time complexity annotations, and the Cost module
  for the definitions of the library primitives used in the analysis.
-}

module RedBlackCost where

import Cost

data Colour :: Integer -> * where
    Black  :: Colour 0
    Red    :: Colour 1
  deriving Show

data Tree :: Integer -> Integer -> Integer -> Nat -> * where
    E   :: forall (lo hi :: Integer) . lo < hi => Tree lo hi 0 0
    TR  :: forall (lo hi :: Integer)(n :: Nat) . pi (x :: Integer) .
                   Tree lo x 0 n -> Tree x hi 0 n -> Tree lo hi 1 n
    TB  :: forall (lo hi cl cr :: Integer)(n :: Nat) . pi (x :: Integer) .
               Tree lo x cl n -> Tree x hi cr n -> Tree lo hi 0 (n+1)
  deriving Show

data RBT :: Integer -> Integer -> * where
    RBT :: forall (lo hi :: Integer)(n :: Nat) . Tree lo hi 0 n -> RBT lo hi
  deriving Show

empty = RBT E

data TreeZip ::  Integer -> Integer -> Integer -> Nat ->
                 Integer -> Integer -> Integer -> Nat -> 
                 Nat -> * where
    Root  :: forall (lo hi c :: Integer)(n :: Nat) . TreeZip lo hi c n lo hi c n 0
    ZRL   :: forall (rlo rhi lo hi rc :: Integer)(rn n d :: Nat) . pi (x :: Integer) .
                 TreeZip rlo rhi rc rn lo hi 1 n d -> Tree x hi 0 n ->
                     TreeZip rlo rhi rc rn lo x 0 n (d + 1)
    ZRR   :: forall (rlo rhi lo hi rc :: Integer)(rn n d :: Nat) . pi (x :: Integer) .
                 Tree lo x 0 n -> TreeZip rlo rhi rc rn lo hi 1 n d ->
                     TreeZip rlo rhi rc rn x hi 0 n (d + 1)
    ZBL   :: forall (rlo rhi lo hi rc c hc :: Integer)(rn n d :: Nat) . pi (x :: Integer) . 
                 TreeZip rlo rhi rc rn lo hi 0 (n+1) d -> Tree x hi c n ->
                     TreeZip rlo rhi rc rn lo x hc n (d + 1)
    ZBR   :: forall (rlo rhi lo hi rc c hc :: Integer)(rn n d :: Nat) . pi (x :: Integer) .
                 Tree lo x c n -> TreeZip rlo rhi rc rn lo hi 0 (n+1) d ->
                     TreeZip rlo rhi rc rn x hi hc n (d + 1)
  deriving Show


plug ::  forall (rlo rhi lo hi rc rn c n d :: Integer) . Tree lo hi c n ->
             TreeZip rlo rhi rc rn lo hi c n d -> Cost (d + 1) (Tree rlo rhi rc rn)
plug t Root           = tick (returnCost t)
plug t (ZRL {x} z r)  = tick (plug (TR {x} t r) z)
plug t (ZRR {x} l z)  = tick (plug (TR {x} l t) z)
plug t (ZBL {x} z r)  = tick (plug (TB {x} t r) z)
plug t (ZBR {x} l z)  = tick (plug (TB {x} l t) z)

plugBR :: forall (rlo rhi lo hi n rn d :: Integer) . Tree lo hi 0 n ->
              TreeZip rlo rhi 0 rn lo hi 1 n d -> Cost (d + 1) (Tree rlo rhi 0 rn)
plugBR t (ZBL {x} z r) = plug t (ZBL {x} z r)
plugBR t (ZBR {x} l z) = plug t (ZBR {x} l z)




data SearchResult :: Integer -> Integer -> Integer -> Integer -> * where
  Nope  :: forall (x rlo rhi lo hi :: Integer)(rn d :: Nat) .
               (d <= (2 * rn), lo < x, x < hi) =>
                   TreeZip rlo rhi 0 rn lo hi 0 0 d -> SearchResult x rlo rhi rn
  Yep   :: forall (x rlo rhi lo hi c :: Integer)(rn n d :: Nat) .
               ((2 * n) + d) <= (2 * rn) =>
                   TreeZip rlo rhi 0 rn lo hi c n d -> Tree lo hi c n ->
                       SearchResult x rlo rhi rn

search ::  forall (rlo rhi :: Integer)(rn :: Nat) .
               pi (x :: Integer) . (rlo < x, x < rhi) =>
                   Tree rlo rhi 0 rn -> Cost (2 * rn + 1) (SearchResult x rlo rhi rn)
search {x} = helpB Root
  where
    help :: forall (lo hi c :: Integer)(n d :: Nat) .
                ((1 + (2 * n) + d) <= (2 * rn), lo < x, x < hi) =>
                    TreeZip rlo rhi 0 rn lo hi c n d -> Tree lo hi c n ->
                        Cost (2 + 2 * n) (SearchResult x rlo rhi rn)
    help z E                      = tick (returnW (Nope z))
    help z (TR {y} l r) | {x < y} = tick (helpB (ZRL {y} z r) l)
    help z (TR {y} l r) | {x ~ y} = tick (returnW (Yep z (TR {y} l r)))
    help z (TR {y} l r) | {x > y} = tick (helpB (ZRR {y} l z) r)
    help z (TB {y} l r) | {x < y} = tick (weakenBy {1} (help (ZBL {y} z r) l))
    help z (TB {y} l r) | {x ~ y} = tick (returnW (Yep z (TB {y} l r)))
    help z (TB {y} l r) | {x > y} = tick (weakenBy {1} (help (ZBR {y} l z) r))

    helpB :: forall (lo hi :: Integer)(n d :: Nat) .
                 (((2 * n) + d) <= (2 * rn), lo < x, x < hi) =>
                     TreeZip rlo rhi 0 rn lo hi 0 n d -> Tree lo hi 0 n ->
                         Cost (2 * n + 1) (SearchResult x rlo rhi rn)
    helpB z E                      = tick (returnW (Nope z))
    helpB z (TB {y} l r) | {x < y} = tick (help (ZBL {y} z r) l)
    helpB z (TB {y} l r) | {x ~ y} = tick (returnW (Yep z (TB {y} l r)))
    helpB z (TB {y} l r) | {x > y} = tick (help (ZBR {y} l z) r)


member ::  forall (lo hi :: Integer)(n :: Nat) .
               pi (x :: Integer) . (lo < x, x < hi) =>
                   Tree lo hi 0 n -> Cost (2 * n + 3) Bool
member {x} t = tick (bindCost (search {x} t) f)
  where
    f :: SearchResult x lo hi n -> Cost 1 Bool
    f (Nope _)   = tick (returnCost False)
    f (Yep _ _)  = tick (returnCost True)


data InsProb :: Integer -> Integer -> Integer -> Integer -> * where
    Level    ::  forall (lo hi c ci :: Integer)( n :: Nat) .
                    Colour ci -> Tree lo hi ci n -> InsProb lo hi c n
    PanicRB  ::  forall (lo hi :: Integer)(n :: Nat) . pi (x :: Integer) .
                    Tree lo x 1 n -> Tree x hi 0 n -> InsProb lo hi 1 n
    PanicBR  ::  forall (lo hi :: Integer)(n :: Nat) . pi (x :: Integer) .
                    Tree lo x 0 n -> Tree x hi 1 n -> InsProb lo hi 1 n
  deriving Show

solveIns :: forall (rlo rhi lo hi c rc :: Integer)(rn n d :: Nat) . 
                InsProb lo hi c n -> TreeZip rlo rhi rc rn lo hi c n d ->
                    Cost (d + 1) (RBT rlo rhi)
solveIns (Level c t)      Root         = tick (returnCost (rbt c t))

solveIns (Level Red t)    (ZRL {x} z r)  = tick (solveIns (PanicRB {x} t r) z)
solveIns (Level Red t)    (ZRR {x} l z)  = tick (solveIns (PanicBR {x} l t) z)
solveIns (Level Black t)  (ZRL {x} z r)  = tick (solveIns (Level Red (TR {x} t r)) z)
solveIns (Level Black t)  (ZRR {x} l z)  = tick (solveIns (Level Red (TR {x} l t)) z)
solveIns (Level col t)    (ZBL {x} z r)  = tick (solveIns (Level Black (TB {x} t r)) z)
solveIns (Level col t)    (ZBR {x} l z)  = tick (solveIns (Level Black (TB {x} l t)) z)

solveIns (PanicRB {xi} (TR {xil} lil ril) ri)  (ZBL {x} z r)  =
    tick (solveIns (Level Red (TR {xi} (TB {xil} lil ril) (TB {x} ri r))) z)
solveIns (PanicBR {xi} li (TR {xir} lir rir))  (ZBL {x} z r)  =
    tick (solveIns (Level Red (TR {xir} (TB {xi} li lir) (TB {x} rir r))) z)

solveIns (PanicRB {xi} (TR {xil} lil ril) ri)  (ZBR {x} l z)  =
    tick (solveIns (Level Red (TR {xil} (TB {x} l lil) (TB {xi} ril ri))) z)
solveIns (PanicBR {xi} li (TR {xir} lir rir))  (ZBR {x} l z)  =
    tick (solveIns (Level Red (TR {xi} (TB {x} l li) (TB {xir} lir rir))) z)




insert ::  forall (lo hi :: Integer)(n :: Nat) . pi (x :: Integer) . (lo < x, x < hi) =>
               Tree lo hi 0 n -> Cost (4 * n + 6) (RBT lo hi)
insert {x} t = tick (bindCost (search {x} t) f)
  where
    f :: SearchResult x lo hi n -> Cost (2 * n + 4) (RBT lo hi)
    f (Nope z)   = tick (weaken (solveIns (Level Red (TR {x} E E)) z))
    f (Yep _ _)  = tick (returnW (RBT t))


r2b :: forall (lo hi n :: Integer) . Tree lo hi 1 n -> Tree lo hi 0 (n+1)
r2b (TR {x} l r) = TB {x} l r

rbt :: forall (lo hi c :: Integer)(n :: Nat) . Colour c -> Tree lo hi c n -> RBT lo hi
rbt Black  t = RBT t
rbt Red    t = RBT (r2b t)





solveDel :: forall (rlo rhi lo hi :: Integer)(rn n d :: Nat) . Tree lo hi 0 n ->
                TreeZip rlo rhi 0 rn lo hi 0 (n+1) d ->
                    Cost (d + 1) (RBT rlo rhi)
solveDel t Root = tick (returnW (RBT t))

solveDel t (ZRL {x} z (TB {y} (TR {lx} ll lr) r)) = tick (mapCost RBT (plug (TR {lx} (TB {x} t ll) (TB {y} lr r)) z))
solveDel t (ZRL {x} z (TB {y} l (TR {rx} rl rr))) = tick (mapCost RBT (plug (TR {y} (TB {x} t l) (TB {rx} rl rr)) z))

-- Arrgh: these are one line in Agda because we can pattern match on the colours being black
solveDel t (ZRL {x} z (TB {y} E E))                = tick (mapCost RBT (plugBR (TB {x} t (TR {y} E E)) z))
solveDel t (ZRL {x} z (TB {y} (TB {lx} ll lr) (TB {rx} rl rr)))  = tick (mapCost RBT (plugBR (TB {x} t (TR {y} (TB {lx} ll lr) (TB {rx} rl rr))) z))


solveDel t (ZRR {x} (TB {y} (TR {lx} ll lr) r) z)  = tick (mapCost RBT (plug (TR {y} (TB {lx} ll lr) (TB {x} r t)) z))
solveDel t (ZRR {x} (TB {y} l (TR {rx} rl rr)) z)  = tick (mapCost RBT (plug (TR {rx} (TB {y} l rl) (TB {x} rr t)) z))

-- Arrgh
solveDel t (ZRR {x} (TB {y} E E) z)              = tick (mapCost RBT (plugBR (TB {y} E (TR {x} E t)) z))
solveDel t (ZRR {x} (TB {y} (TB {lx} ll lr) (TB {rx} rl rr)) z)  = tick (mapCost RBT (plugBR (TB {y} (TB {lx} ll lr) (TR {x} (TB {rx} rl rr) t)) z))


-- Arrgh
solveDel t (ZBL {x} z (TR {y} (TB {lx} E lr) r))  = tick (mapCost RBT (plug (TB {y} (TB {lx} (TR {x} t E) lr) r) z))
solveDel t (ZBL {x} z (TR {y} (TB {lx} (TB {llx} lll llr) lr) r))  = tick (mapCost RBT (plug (TB {y} (TB {lx} (TR {x} t (TB {llx} lll llr)) lr) r) z))

solveDel t (ZBL {x} z (TR {y} (TB {lx} (TR {llx} lll llr) lr) r))  = tick (mapCost RBT (plug (TB {llx} (TB {x} t lll) (TR {y} (TB {lx} llr lr) r)) z))

-- Arrgh
solveDel t (ZBL {x} z (TB {y} E r)) = tick (solveDel (TB {y} (TR {x} t E) r) z)
solveDel t (ZBL {x} z (TB {y} (TB {lx} ll lr) r))  = tick (solveDel (TB {y} (TR {x} t (TB {lx} ll lr)) r) z)

-- Arrgh
solveDel t (ZBL {x} z (TB {y} (TR {lx} ll lr) E))  = tick (solveDel (TB {lx} (TR {x} t ll) (TR {y} lr E)) z)
solveDel t (ZBL {x} z (TB {y} (TR {lx} ll lr) (TB {rx} rl rr)))  = tick (solveDel (TB {lx} (TR {x} t ll) (TR {y} lr (TB {rx} rl rr))) z)

solveDel t (ZBL {x} z (TB {y} (TR {lx} ll lr) (TR {rx} rl rr))) = tick (mapCost RBT (plug (TB {lx} (TB {x} t ll) (TB {y} lr (TR {rx} rl rr))) z))


-- Arrgh
solveDel t (ZBR {x} (TR {y} l (TB {rx} rl E)) z) = tick (mapCost RBT (plug (TB {y} l (TB {rx} rl (TR {x} E t))) z))
solveDel t (ZBR {x} (TR {y} l (TB {rx} rl (TB {rrx} rrl rrr))) z)  = tick (mapCost RBT (plug (TB {y} l (TB {rx} rl (TR {x} (TB {rrx} rrl rrr) t))) z))

solveDel t (ZBR {x} (TR {y} l (TB {rx} rl (TR {rrx} rrl rrr))) z)  = tick (mapCost RBT (plug (TB {rrx} (TR {y} l (TB {rx} rl rrl)) (TB {x} rrr t)) z))

-- Arrgh
solveDel t (ZBR {x} (TB {y} l E) z)  = tick (solveDel (TB {y} l (TR {x} E t)) z)
solveDel t (ZBR {x} (TB {y} l (TB {lx} ll lr)) z)  = tick (solveDel (TB {y} l (TR {x} (TB {lx} ll lr) t)) z)

-- Arrgh
solveDel t (ZBR {x} (TB {y} E (TR {rx} rl rr)) z)  = tick (solveDel (TB {rx} (TR {y} E rl) (TR {x} rr t)) z)
solveDel t (ZBR {x} (TB {y} (TB {lx} ll lr) (TR {rx} rl rr)) z)  = tick (solveDel (TB {rx} (TR {y} (TB {lx} ll lr) rl) (TR {x} rr t)) z)

solveDel t (ZBR {x} (TB {y} (TR {lx} ll lr) (TR {rx} rl rr)) z) = tick (mapCost RBT (plug (TB {y} (TB {lx} ll lr) (TB {rx} rl (TR {x} rr t))) z))


findMin :: forall (rlo rhi lo hi c :: Integer)(rn n d :: Nat) . Tree lo hi c (n+1) ->
               (pi (k :: Integer) . lo < k => TreeZip rlo rhi 0 rn k hi c (n+1) d) ->
                   Cost (3 * n + d + 4) (RBT rlo rhi)
findMin (TR {x} (TB {y} E E) r)                    f = tick (weaken (solveDel E (ZRL {x} (f {y}) r)))
findMin (TR {x} (TB {y} E (TR {lx} ll lr)) r)      f = tick (weaken (mapCost RBT (plug (TB {lx} ll lr) (ZRL {x} (f {y}) r))))

findMin (TR {x} (TB {y} (TR {k} E E) lr) r)        f = tick (weaken (mapCost RBT (plug E (ZBL {y} (ZRL {x} (f {k}) r) lr))))

findMin (TB {x} (TR {y} E E) r)                    f = tick (weaken (mapCost RBT (plug E (ZBL {x} (f {y}) r))))
findMin (TB {x} E (TR {lx} ll lr))                 f = tick (weaken (mapCost RBT (plug (TB {lx} ll lr) (f {x}))))
findMin (TB {x} E E)                               f = tick (weaken (solveDel E (f {x})))

findMin (TR {x} (TB {y} (TB {llx} lll llr) lr) r)  f = tick (findMin (TB {llx} lll llr) (\ {k} -> ZBL {y} (ZRL {x} (f {k}) r) lr))
findMin (TB {x} (TB {lx} ll lr) r)                 f = tick (weakenBy {1} (findMin (TB {lx} ll lr)  (\ {k} -> ZBL {x} (f {k}) r)))



wkTree :: forall (lo hi ha c n :: Integer) . hi < ha => Tree lo hi c n -> Tree lo ha c n
wkTree E            = E
wkTree (TR {x} l r) = TR {x} l (wkTree r)
wkTree (TB {x} l r) = TB {x} l (wkTree r)

delFocus :: forall (rlo rhi lo hi c :: Integer)(rn n d :: Nat) . Tree lo hi c n ->
                TreeZip rlo rhi 0 rn lo hi c n d ->
                    Cost (3 * n + d + 3) (RBT rlo rhi)
delFocus (TR {x} E E)                        z = tick (weakenBy {1} (mapCost RBT (plugBR E z)))
delFocus (TR {x} l (TB {rx} rl rr))          z = tick (findMin (TB {rx} rl rr) (\ {k} -> ZRR {k} (wkTree l) z))
delFocus E                                   z = tick (weaken (mapCost RBT (plug E z)))
delFocus (TB {x} E E)                        z = tick (weaken (solveDel E z))
delFocus (TB {x} (TR {y} E E) E)             z = tick (weaken (mapCost RBT (plug (TB {y} E E) z)))
delFocus (TB {x} E (TR {y} E E))             z = tick (weaken (mapCost RBT (plug (TB {y} E E) z)))
delFocus (TB {x} (TR {k} E E) (TR {y} E E))  z = tick (weaken (mapCost RBT (plug (TB {k} E (TR {y} E E)) z)))
delFocus (TB {x} l (TB {rx} rl rr))          z = tick (weakenBy {3} (findMin (TB {rx} rl rr) (\ {k} -> ZBR {k} (wkTree l) z)))
delFocus (TB {x} (TB {lx} ll lr)  r)         z = tick (weakenBy {3} (findMin r (\ {k} -> ZBR {k} (wkTree (TB {lx} ll lr)) z)))


delete :: forall (lo hi :: Integer)(n :: Nat) . pi (x :: Integer) . (lo < x, x < hi) =>
           Tree lo hi 0 n -> Cost (5 * n + 6) (RBT lo hi)
delete {x} t = tick (bindCost (search {x} t) f)
  where
    f :: SearchResult x lo hi n -> Cost (3 * n + 4) (RBT lo hi)
    f (Nope _)   = tick (returnW (RBT t))
    f (Yep z t)  = tick (weaken (delFocus t z))
