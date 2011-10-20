{-# OPTIONS_GHC -F -pgmF ./toy #-}

{-# LANGUAGE GADTs, RankNTypes, KindSignatures, ScopedTypeVariables, NPlusKPatterns #-}

module RedBlackOrdCost where

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

data Tree :: Num -> Num -> Num -> Num -> * where
  E   :: forall (lo hi :: Num) . lo < hi => Tree lo hi 0 0
  TR  :: forall (lo hi :: Num)(n :: Nat) . pi (x :: Num) .
                 Tree lo x 0 n -> Tree x hi 0 n -> Tree lo hi 1 n
  TB  :: forall (lo hi cl cr :: Num)(n :: Nat) . pi (x :: Num) .
             Tree lo x cl n -> Tree x hi cr n -> Tree lo hi 0 (n+1)


data RBT :: Num -> Num -> * where
  RBT :: forall (lo hi :: Num)(n :: Nat) . Tree lo hi 0 n -> RBT lo hi

empty = RBT E





data T where
  T :: forall (n :: Nat)(lo hi :: Num) . Tree lo hi 0 n -> T

emptyT = T E

rbtToT :: forall (lo hi :: Num) . RBT lo hi -> T
rbtToT (RBT t) = T t

insertT :: pi (x :: Num) . T -> T
insertT {x} (T t) = rbtToT (insert {x} (RBT (weakling {x} t)))

deleteT :: pi (x :: Num) . T -> T
deleteT {x} (T t) = rbtToT (delete {x} (RBT (weakling {x} t)))

weakling :: forall (lo hi c n :: Num) . pi (x :: Num) . Tree lo hi c n ->
              Tree (min lo (x-1)) (max hi (x+1)) c n
weakling {x} t = wkTree2 t

wkTree2 :: forall (lo lo' hi hi' c n :: Num) . lo' <= lo, hi <= hi' =>
               Tree lo hi c n -> Tree lo' hi' c n
wkTree2 E            = E
wkTree2 (TR {x} l r) = TR {x} (wkTree2 l) (wkTree2 r)
wkTree2 (TB {x} l r) = TB {x} (wkTree2 l) (wkTree2 r)




data TreeZip :: Num -> Num -> Num -> Num -> Num -> Num -> Num -> Num -> Num -> * where
  Root  :: forall (lo hi c :: Num)(n :: Nat) . TreeZip lo hi c n lo hi c n 0
  ZRL   :: forall (rlo rhi lo hi rc :: Num)(rn n d :: Nat) . pi (x :: Num) .
               TreeZip rlo rhi rc rn lo hi 1 n d -> Tree x hi 0 n ->
                   TreeZip rlo rhi rc rn lo x 0 n (d + 1)
  ZRR   :: forall (rlo rhi lo hi rc :: Num)(rn n d :: Nat) . pi (x :: Num) .
               Tree lo x 0 n -> TreeZip rlo rhi rc rn lo hi 1 n d ->
                   TreeZip rlo rhi rc rn x hi 0 n (d + 1)
  ZBL   :: forall (rlo rhi lo hi rc c hc :: Num)(rn n d :: Nat) . pi (x :: Num) . 
               TreeZip rlo rhi rc rn lo hi 0 (n+1) d -> Tree x hi c n ->
                   TreeZip rlo rhi rc rn lo x hc n (d + 1)
  ZBR   :: forall (rlo rhi lo hi rc c hc :: Num)(rn n d :: Nat) . pi (x :: Num) .
               Tree lo x c n -> TreeZip rlo rhi rc rn lo hi 0 (n+1) d ->
                   TreeZip rlo rhi rc rn x hi hc n (d + 1)


plug ::  forall (rlo rhi lo hi rc rn c n d :: Num) . Tree lo hi c n ->
             TreeZip rlo rhi rc rn lo hi c n d -> Cost (d + 1) (Tree rlo rhi rc rn)
plug t Root           = tick (ret t)
plug t (ZRL {x} z r)  = tick (plug (TR {x} t r) z)
plug t (ZRR {x} l z)  = tick (plug (TR {x} l t) z)
plug t (ZBL {x} z r)  = tick (plug (TB {x} t r) z)
plug t (ZBR {x} l z)  = tick (plug (TB {x} l t) z)

plugBR :: forall (rlo rhi lo hi n rn d :: Num) . Tree lo hi 0 n ->
              TreeZip rlo rhi 0 rn lo hi 1 n d -> Cost (d + 1) (Tree rlo rhi 0 rn)
plugBR t (ZBL {x} z r) = plug t (ZBL {x} z r)
plugBR t (ZBR {x} l z) = plug t (ZBR {x} l z)


search :: forall p (rlo rhi :: Num)(rn :: Nat) . pi (x :: Num) . rlo < x, x < rhi => p ->
              (forall (lo hi :: Num)(d :: Nat) . d <= (2 * rn), lo < x, x < hi =>
                  TreeZip rlo rhi 0 rn lo hi 0 0 d -> p) ->
              (forall (lo hi c :: Num)(n d :: Nat) . ((2 * n) + d) <= (2 * rn) =>
                  TreeZip rlo rhi 0 rn lo hi c n d -> Tree lo hi c n -> p) ->
              Tree rlo rhi 0 rn -> Cost (2 * rn + 1) p
search {x} _ fe fn = 
  let
    help :: forall (lo hi c :: Num)(n d :: Nat) . (1 + (2 * n) + d) <= (2 * rn), lo < x, x < hi =>
                TreeZip rlo rhi 0 rn lo hi c n d -> Tree lo hi c n -> Cost (2 + 2 * n) p
    help z E                      = tick (returnW (fe z))
    help z (TR {y} l r) | {x < y} = tick (helpB (ZRL {y} z r) l)
    help z (TR {y} l r) | {x ~ y} = tick (returnW (fn z (TR {y} l r)))
    help z (TR {y} l r) | {x > y} = tick (helpB (ZRR {y} l z) r)
    help z (TB {y} l r) | {x < y} = tick (weaken {1} (help (ZBL {y} z r) l))
    help z (TB {y} l r) | {x ~ y} = tick (returnW (fn z (TB {y} l r)))
    help z (TB {y} l r) | {x > y} = tick (weaken {1} (help (ZBR {y} l z) r))

    helpB :: forall (lo hi :: Num)(n d :: Nat) . ((2 * n) + d) <= (2 * rn), lo < x, x < hi =>
                TreeZip rlo rhi 0 rn lo hi 0 n d -> Tree lo hi 0 n -> Cost (1 + 2 * n) p
    helpB z E                      = tick (returnW (fe z))
    helpB z (TB {y} l r) | {x < y} = tick (help (ZBL {y} z r) l)
    helpB z (TB {y} l r) | {x ~ y} = tick (returnW (fn z (TB {y} l r)))
    helpB z (TB {y} l r) | {x > y} = tick (help (ZBR {y} l z) r)

  in helpB Root


member :: forall (lo hi :: Num)(n :: Nat) . pi (x :: Num) . lo < x, x < hi =>
              Tree lo hi 0 n -> Bool
member {x} t = force (search {x} undefined (\ z -> False) (\ z zz -> True) t)




data ColTree :: Num -> Num -> Num -> * where
  CT :: forall (lo hi c :: Num)(n :: Nat) .
            Colour c -> Tree lo hi c n -> ColTree lo hi n



data InsProb :: Num -> Num -> Num -> Num -> * where
  Level    :: forall (lo hi c ci :: Num)( n :: Nat) .
                  Colour ci -> Tree lo hi ci n -> InsProb lo hi c n
  PanicRB  :: forall (lo hi :: Num)(n :: Nat) . pi (x :: Num) .
                  Tree lo x 1 n -> Tree x hi 0 n -> InsProb lo hi 1 n
  PanicBR  :: forall (lo hi :: Num)(n :: Nat) . pi (x :: Num) .
                  Tree lo x 0 n -> Tree x hi 1 n -> InsProb lo hi 1 n

solveIns :: forall (rlo rhi lo hi c rc :: Num)(rn n d :: Nat) . 
                InsProb lo hi c n -> TreeZip rlo rhi rc rn lo hi c n d ->
                    Cost (d + 1) (ColTree rlo rhi rn)
solveIns (Level c t)      Root         = tick (ret (CT c t))

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


data SearchResult :: Num -> Num -> Num -> Num -> * where
  Nope  :: forall (x rlo rhi lo hi :: Num)(rn d :: Nat) .
               d <= (2 * rn), lo < x, x < hi =>
                   TreeZip rlo rhi 0 rn lo hi 0 0 d -> SearchResult x rlo rhi rn
  Yep   :: forall (x rlo rhi lo hi c :: Num)(rn n d :: Nat) .
               ((2 * n) + d) <= (2 * rn) =>
                   TreeZip rlo rhi 0 rn lo hi c n d -> Tree lo hi c n ->
                       SearchResult x rlo rhi rn

search2 :: forall (rlo rhi :: Num)(rn :: Nat) . pi (x :: Num) . rlo < x, x < rhi =>
                  Tree rlo rhi 0 rn -> Cost (2 * rn + 1) (SearchResult x rlo rhi rn)
search2 {x} = 
  let
    help :: forall (lo hi c :: Num)(n d :: Nat) .
                (1 + (2 * n) + d) <= (2 * rn), lo < x, x < hi =>
                    TreeZip rlo rhi 0 rn lo hi c n d -> Tree lo hi c n ->
                        Cost (2 + 2 * n) (SearchResult x rlo rhi rn)
    help z E                      = tick (returnW (Nope z))
    help z (TR {y} l r) | {x < y} = tick (helpB (ZRL {y} z r) l)
    help z (TR {y} l r) | {x ~ y} = tick (returnW (Yep z (TR {y} l r)))
    help z (TR {y} l r) | {x > y} = tick (helpB (ZRR {y} l z) r)
    help z (TB {y} l r) | {x < y} = tick (weaken {1} (help (ZBL {y} z r) l))
    help z (TB {y} l r) | {x ~ y} = tick (returnW (Yep z (TB {y} l r)))
    help z (TB {y} l r) | {x > y} = tick (weaken {1} (help (ZBR {y} l z) r))

    helpB :: forall (lo hi :: Num)(n d :: Nat) .
                 ((2 * n) + d) <= (2 * rn), lo < x, x < hi =>
                     TreeZip rlo rhi 0 rn lo hi 0 n d -> Tree lo hi 0 n ->
                         Cost (2 * n + 1) (SearchResult x rlo rhi rn)
    helpB z E                      = tick (returnW (Nope z))
    helpB z (TB {y} l r) | {x < y} = tick (help (ZBL {y} z r) l)
    helpB z (TB {y} l r) | {x ~ y} = tick (returnW (Yep z (TB {y} l r)))
    helpB z (TB {y} l r) | {x > y} = tick (help (ZBR {y} l z) r)

  in helpB Root

ins :: forall (l h :: Num)(n :: Nat) . pi (x :: Num) . l < x, x < h =>
           Tree l h 0 n -> Cost (4 * n + 5) (ColTree l h n)
ins {x} t = 
  let 
    f :: SearchResult x l h n -> Cost (2 * n + 3) (ColTree l h n)
    f (Nope z)   = tick (magicweak (solveIns (Level Red (TR {x} E E)) z))
    f (Yep _ _)  = tick (returnW (CT Black t))
  in tick (bind (search2 {x} t) f)




r2b :: forall (lo hi n :: Num) . Tree lo hi 1 n -> Tree lo hi 0 (n+1)
r2b (TR {x} l r) = TB {x} l r

unCT :: forall (lo hi n :: Num) . ColTree lo hi n -> RBT lo hi
unCT (CT Black t)  = RBT t
unCT (CT Red t)    = RBT (r2b t)


insert :: forall (lo hi :: Num) . pi (x :: Num) . lo < x, x < hi =>
              RBT lo hi -> RBT lo hi
insert {x} (RBT t) = unCT (force (ins {x} t))





solveDel :: forall (rlo rhi lo hi :: Num)(rn n d :: Nat) . Tree lo hi 0 n ->
                TreeZip rlo rhi 0 rn lo hi 0 (n+1) d ->
                    Cost (d + 1) (RBT rlo rhi)
solveDel t Root = tick (returnW (RBT t))

solveDel t (ZRL {x} z (TB {y} (TR {lx} ll lr) r)) = tick (fmp RBT (plug (TR {lx} (TB {x} t ll) (TB {y} lr r)) z))
solveDel t (ZRL {x} z (TB {y} l (TR {rx} rl rr))) = tick (fmp RBT (plug (TR {y} (TB {x} t l) (TB {rx} rl rr)) z))

-- Arrgh: these are one line in Agda because we can pattern match on the colours being black
solveDel t (ZRL {x} z (TB {y} E E))                = tick (fmp RBT (plugBR (TB {x} t (TR {y} E E)) z))
solveDel t (ZRL {x} z (TB {y} (TB {lx} ll lr) (TB {rx} rl rr)))  = tick (fmp RBT (plugBR (TB {x} t (TR {y} (TB {lx} ll lr) (TB {rx} rl rr))) z))


solveDel t (ZRR {x} (TB {y} (TR {lx} ll lr) r) z)  = tick (fmp RBT (plug (TR {y} (TB {lx} ll lr) (TB {x} r t)) z))
solveDel t (ZRR {x} (TB {y} l (TR {rx} rl rr)) z)  = tick (fmp RBT (plug (TR {rx} (TB {y} l rl) (TB {x} rr t)) z))

-- Arrgh
solveDel t (ZRR {x} (TB {y} E E) z)              = tick (fmp RBT (plugBR (TB {y} E (TR {x} E t)) z))
solveDel t (ZRR {x} (TB {y} (TB {lx} ll lr) (TB {rx} rl rr)) z)  = tick (fmp RBT (plugBR (TB {y} (TB {lx} ll lr) (TR {x} (TB {rx} rl rr) t)) z))


-- Arrgh
solveDel t (ZBL {x} z (TR {y} (TB {lx} E lr) r))  = tick (fmp RBT (plug (TB {y} (TB {lx} (TR {x} t E) lr) r) z))
solveDel t (ZBL {x} z (TR {y} (TB {lx} (TB {llx} lll llr) lr) r))  = tick (fmp RBT (plug (TB {y} (TB {lx} (TR {x} t (TB {llx} lll llr)) lr) r) z))

solveDel t (ZBL {x} z (TR {y} (TB {lx} (TR {llx} lll llr) lr) r))  = tick (fmp RBT (plug (TB {llx} (TB {x} t lll) (TR {y} (TB {lx} llr lr) r)) z))

-- Arrgh
solveDel t (ZBL {x} z (TB {y} E r)) = tick (solveDel (TB {y} (TR {x} t E) r) z)
solveDel t (ZBL {x} z (TB {y} (TB {lx} ll lr) r))  = tick (solveDel (TB {y} (TR {x} t (TB {lx} ll lr)) r) z)

-- Arrgh
solveDel t (ZBL {x} z (TB {y} (TR {lx} ll lr) E))  = tick (solveDel (TB {lx} (TR {x} t ll) (TR {y} lr E)) z)
solveDel t (ZBL {x} z (TB {y} (TR {lx} ll lr) (TB {rx} rl rr)))  = tick (solveDel (TB {lx} (TR {x} t ll) (TR {y} lr (TB {rx} rl rr))) z)

solveDel t (ZBL {x} z (TB {y} (TR {lx} ll lr) (TR {rx} rl rr))) = tick (fmp RBT (plug (TB {lx} (TB {x} t ll) (TB {y} lr (TR {rx} rl rr))) z))


-- Arrgh
solveDel t (ZBR {x} (TR {y} l (TB {rx} rl E)) z) = tick (fmp RBT (plug (TB {y} l (TB {rx} rl (TR {x} E t))) z))
solveDel t (ZBR {x} (TR {y} l (TB {rx} rl (TB {rrx} rrl rrr))) z)  = tick (fmp RBT (plug (TB {y} l (TB {rx} rl (TR {x} (TB {rrx} rrl rrr) t))) z))

solveDel t (ZBR {x} (TR {y} l (TB {rx} rl (TR {rrx} rrl rrr))) z)  = tick (fmp RBT (plug (TB {rrx} (TR {y} l (TB {rx} rl rrl)) (TB {x} rrr t)) z))

-- Arrgh
solveDel t (ZBR {x} (TB {y} l E) z)  = tick (solveDel (TB {y} l (TR {x} E t)) z)
solveDel t (ZBR {x} (TB {y} l (TB {lx} ll lr)) z)  = tick (solveDel (TB {y} l (TR {x} (TB {lx} ll lr) t)) z)

-- Arrgh
solveDel t (ZBR {x} (TB {y} E (TR {rx} rl rr)) z)  = tick (solveDel (TB {rx} (TR {y} E rl) (TR {x} rr t)) z)
solveDel t (ZBR {x} (TB {y} (TB {lx} ll lr) (TR {rx} rl rr)) z)  = tick (solveDel (TB {rx} (TR {y} (TB {lx} ll lr) rl) (TR {x} rr t)) z)

solveDel t (ZBR {x} (TB {y} (TR {lx} ll lr) (TR {rx} rl rr)) z) = tick (fmp RBT (plug (TB {y} (TB {lx} ll lr) (TB {rx} rl (TR {x} rr t))) z))


findMin :: forall (rlo rhi lo hi c :: Num)(rn n d :: Nat) . Tree lo hi c (n+1) ->
               (pi (k :: Num) . lo < k => TreeZip rlo rhi 0 rn k hi c (n+1) d) ->
                   Cost (3 * n + d + 4) (RBT rlo rhi)
findMin (TR {x} (TB {y} E E) r)                    f = tick (magicweak (solveDel E (ZRL {x} (f {y}) r)))
findMin (TR {x} (TB {y} E (TR {lx} ll lr)) r)      f = tick (magicweak (fmp RBT (plug (TB {lx} ll lr) (ZRL {x} (f {y}) r))))

findMin (TR {x} (TB {y} (TR {k} E E) lr) r)          f = tick (magicweak (fmp RBT (plug E (ZBL {y} (ZRL {x} (f {k}) r) lr))))

findMin (TB {x} (TR {y} E E) r)                    f = tick (magicweak (fmp RBT (plug E (ZBL {x} (f {y}) r))))
findMin (TB {x} E (TR {lx} ll lr))                 f = tick (magicweak (fmp RBT (plug (TB {lx} ll lr) (f {x}))))
findMin (TB {x} E E)                               f = tick (magicweak (solveDel E (f {x})))

findMin (TR {x} (TB {y} (TB {llx} lll llr) lr) r)  f = tick (findMin (TB {llx} lll llr) (\ {k} -> ZBL {y} (ZRL {x} (f {k}) r) lr))
findMin (TB {x} (TB {lx} ll lr) r)                 f = tick (weaken {1} (findMin (TB {lx} ll lr)  (\ {k} -> ZBL {x} (f {k}) r)))



wkTree :: forall (lo hi ha c n :: Num) . hi < ha => Tree lo hi c n -> Tree lo ha c n
wkTree E            = E
wkTree (TR {x} l r) = TR {x} l (wkTree r)
wkTree (TB {x} l r) = TB {x} l (wkTree r)

delFocus :: forall (rlo rhi lo hi c :: Num)(rn n d :: Nat) . Tree lo hi c n ->
                TreeZip rlo rhi 0 rn lo hi c n d ->
                    Cost (3 * n + d + 3) (RBT rlo rhi)
delFocus (TR {x} E E)                        z = tick (weaken {1} (fmp RBT (plugBR E z)))
delFocus (TR {x} l (TB {rx} rl rr))          z = tick (findMin (TB {rx} rl rr) (\ {k} -> ZRR {k} (wkTree l) z))
delFocus E                                   z = tick (magicweak (fmp RBT (plug E z)))
delFocus (TB {x} E E)                        z = tick (magicweak (solveDel E z))
delFocus (TB {x} (TR {y} E E) E)             z = tick (magicweak (fmp RBT (plug (TB {y} E E) z)))
delFocus (TB {x} E (TR {y} E E))             z = tick (magicweak (fmp RBT (plug (TB {y} E E) z)))
delFocus (TB {x} (TR {k} E E) (TR {y} E E))  z = tick (magicweak (fmp RBT (plug (TB {k} E (TR {y} E E)) z)))
delFocus (TB {x} l (TB {rx} rl rr))          z = tick (weaken {3} (findMin (TB {rx} rl rr) (\ {k} -> ZBR {k} (wkTree l) z)))
delFocus (TB {x} (TB {lx} ll lr)  r)         z = tick (weaken {3} (findMin r (\ {k} -> ZBR {k} (wkTree (TB {lx} ll lr)) z)))






del :: forall (lo hi :: Num)(n :: Nat) . pi (x :: Num) . lo < x, x < hi =>
           Tree lo hi 0 n -> Cost (5 * n + 6) (RBT lo hi)
del {x} t = 
  let 
    f :: SearchResult x lo hi n -> Cost (3 * n + 4) (RBT lo hi)
    f (Nope _)   = tick (returnW (RBT t))
    f (Yep z t)  = tick (magicweak (delFocus t z))
  in tick (bind (search2 {x} t) f)

delete :: forall (lo hi :: Num) . pi (x :: Num) . lo < x, x < hi =>
              RBT lo hi -> RBT lo hi
delete {x} (RBT t) = force (del {x} t)
