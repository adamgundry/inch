> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
>              GADTs, TypeOperators, FlexibleInstances,
>              StandaloneDeriving, TypeFamilies, RankNTypes,
>              ImpredicativeTypes, FlexibleContexts,
>              MultiParamTypeClasses, EmptyDataDecls,
>              UndecidableInstances #-}

> module Language.Inch.Syntax where

> import Control.Applicative
> import Data.Traversable
> import Data.Monoid hiding (All)
> import Unsafe.Coerce

> import Language.Inch.Kit
> import Language.Inch.Kind
> import Language.Inch.Type


> listTypeName, listNilName, listConsName :: String
> listTypeName  = "[]"
> listNilName   = "[]"
> listConsName  = "(:)"

> unitTypeName, unitConsName :: String
> unitTypeName = "()"
> unitConsName = "()"

> tupleTypeName, tupleConsName :: String
> tupleTypeName = "(,)"
> tupleConsName = "(,)"


> data OK
> data RAW

> type family AKind s k
> type instance AKind OK k   = Kind k
> type instance AKind RAW k  = SKind

> type family ATy s a k
> type instance ATy OK   a k = Ty a k
> type instance ATy RAW  a k = SType

> type AType s k = ATy s () k

> type family AVar s a k
> type instance AVar OK   a k = Var a k
> type instance AVar RAW  a k = String


> type Con s        = TmConName ::: ATy s () KSet

> type Term             = Tm OK
> type Constructor      = Con OK
> type Alternative      = Alt OK
> type CaseAlternative  = CaseAlt OK
> type PatternList      = PatList OK
> type Pattern          = Pat OK
> type Declaration      = Decl OK
> type Guard            = Grd OK
> type GuardTerms       = GrdTms OK

> type STerm             = Tm RAW
> type SConstructor      = Con RAW
> type SAlternative      = Alt RAW
> type SCaseAlternative  = CaseAlt RAW
> type SPatternList      = PatList RAW
> type SPattern          = Pat RAW
> type SDeclaration      = Decl RAW
> type SGuard            = Grd RAW
> type SGuardTerms       = GrdTms RAW



> class TravTypes t where
>     travTypes :: Applicative f =>
>          (forall a k . Ty a k -> f (Ty a k)) -> t OK -> f (t OK)
>     fogTypes :: (forall k. Var () k -> String) -> t OK -> t RAW
>     renameTypes :: (forall k . Var () k -> Var () k) -> t OK -> t OK


> class TravTypes1 t where
>     travTypes1 :: Applicative f =>
>          (forall a k . Ty a k -> f (Ty a k)) -> t OK b -> f (t OK b)
>     fogTypes1 :: (forall k. Var a k -> String) -> t OK a -> t RAW a
>     renameTypes1 :: (forall k . Var a k -> Var c k) -> t OK a -> t OK c
>     rawCoerce :: t RAW a -> t RAW c
>     rawCoerce = unsafeCoerce

> class TravTypes2 t where
>     fogTypes2 :: (forall k . Var a k -> String) -> t OK a b ->
>                     (t RAW a b, (forall k . Var b k -> String))
>     renameTypes2 ::
>         (forall k . Var a k -> Var c k) -> VarSuffix a b x -> t OK a b ->
>             (forall d . VarSuffix c d x -> t OK c d -> p) ->
>                 p
>
>     rawCoerce2 :: t RAW a b -> t RAW c d
>     rawCoerce2 = unsafeCoerce
>

>     ext :: t OK a b -> (forall x . VarSuffix a b x -> p) -> p

> class FV2 t where
>     fvFoldMap2 :: Monoid m => (forall k . Var a k -> m) -> t OK a b -> (m, (forall k. Var b k -> m))

> mapTypes :: TravTypes1 t =>
>                 (forall a k. Ty a k -> Ty a k) -> t OK b -> t OK b
> mapTypes g = unId . travTypes1 (Id . g)

> replaceTypes :: TravTypes1 t => Var () k -> Type k -> t OK a -> t OK a
> replaceTypes a t = mapTypes (replaceTy (wkClosedVar a) (wkClosedTy t))

> bindTm :: TravTypes1 t => Var a k -> t OK a -> t OK (a, k)
> bindTm v = renameTypes1 (bindVar v)

> unbindTm :: TravTypes1 t => Var c k -> t OK (c, k) -> t OK c
> unbindTm v = renameTypes1 (unbindVar v)

> fog :: TravTypes t => t OK -> t RAW
> fog = fogTypes fogVar

> fog1 :: TravTypes1 t => t OK () -> t RAW ()
> fog1 = fogTypes1 fogVar

> fogSys :: TravTypes1 t => t OK () -> t RAW ()
> fogSys = fogTypes1 fogSysVar

> fogSys2 :: TravTypes2 t => t OK () a -> t RAW () a
> fogSys2 = fst . fogTypes2 fogSysVar

> bindUn :: TravTypes2 t =>
>             Var a k -> VarSuffix a b x -> t OK a b ->
>              (forall d . VarSuffix (a, k) d x -> t OK (a, k) d -> p) -> p
> bindUn v vs t q = renameTypes2 (bindVar v) vs t q



> data (:*:) f g a b where
>     (:*:) :: f a b -> g a b -> (:*:) f g a b 

> deriving instance (Show (f s a), Show (g s a)) => Show ((:*:) f g s a)

> instance (Eq (f RAW b), Eq (g RAW b)) => Eq ((f :*: g) RAW b) where
>     x :*: y == x' :*: y'  =  x == x' && y == y'

> instance (TravTypes1 f, TravTypes1 g) => TravTypes1 (f :*: g) where
>     travTypes1    g (x :*: y) = (:*:) <$> travTypes1 g x <*> travTypes1 g y
>     fogTypes1     g (x :*: y) = fogTypes1 g x     :*: fogTypes1 g y
>     renameTypes1  g (x :*: y) = renameTypes1 g x  :*: renameTypes1 g y

> instance (FV (f s a) a, FV (g s a) a) => FV ((f :*: g) s a) a where
>     fvFoldMap f (x :*: y) = fvFoldMap f x <.> fvFoldMap f y

> {-
> data (:+:) f g a b where
>     InL  :: f a b -> (f :+: g) a b 
>     InR  :: g a b -> (f :+: g) a b 

> instance (Eq (f RAW b), Eq (g RAW b)) => Eq ((f :+: g) RAW b) where
>     InL x  == InL y  =  x == y
>     InR x  == InR y  =  x == y
>     _      == _      =  False

> instance (TravTypes f, TravTypes g) => TravTypes (f :+: g) where
>     travTypes    g (InL x) = InL <$> travTypes g x
>     travTypes    g (InR x) = InR <$> travTypes g x
>     fogTypes     g (InL x) = InL (fogTypes g x)
>     fogTypes     g (InR x) = InR (fogTypes g x)
>     renameTypes  g (InL x) = InL (renameTypes g x)
>     renameTypes  g (InR x) = InR (renameTypes g x)
> -}










> data Tm s a where
>     TmVar    :: TmName                    -> Tm s a
>     TmCon    :: TmConName                 -> Tm s a
>     TmInt    :: Integer                   -> Tm s a
>     CharLit  :: Char                      -> Tm s a
>     StrLit   :: String                    -> Tm s a
>     TmApp    :: Tm s a -> Tm s a          -> Tm s a
>     TmBrace  :: ATy s a KNum              -> Tm s a
>     Lam      :: TmName -> Tm s a          -> Tm s a
>     NumLam   :: String -> Tm s (a, KNum)  -> Tm s a
>     Let      :: [Decl s a] -> Tm s a      -> Tm s a
>     Case     :: Tm s a -> [CaseAlt s a]   -> Tm s a
>     (:?)     :: Tm s a -> ATy s a KSet    -> Tm s a

> deriving instance Show (Tm RAW a)
> deriving instance Show (Tm OK a)
> deriving instance Eq (Tm RAW a)

> instance TravTypes1 Tm where

>     travTypes1 g (TmApp f s)  = TmApp <$> travTypes1 g f <*> travTypes1 g s
>     travTypes1 g (TmBrace n)  = TmBrace <$> g n
>     travTypes1 g (Lam x b)    = Lam x <$> travTypes1 g b
>     travTypes1 g (NumLam a b) = NumLam a <$> travTypes1 g b 
>     travTypes1 g (Let ds t)   = Let <$> traverse (travTypes1 g) ds
>                                    <*> travTypes1 g t
>     travTypes1 g (t :? ty)    = (:?) <$> travTypes1 g t <*> g ty
>     travTypes1 _ t            = pure t

>     fogTypes1 _ (TmVar x)     = TmVar x
>     fogTypes1 _ (TmCon c)     = TmCon c
>     fogTypes1 _ (TmInt k)     = TmInt k
>     fogTypes1 _ (CharLit c)   = CharLit c
>     fogTypes1 _ (StrLit s)    = StrLit s
>     fogTypes1 g (TmApp f s)   = TmApp (fogTypes1 g f) (fogTypes1 g s)
>     fogTypes1 g (TmBrace n)   = TmBrace (fogTy' g [] n)
>     fogTypes1 g (Lam x b)     = Lam x (fogTypes1 g b)
>     fogTypes1 g (NumLam x b)  = NumLam x (fogTypes1 (wkF g x) b)
>     fogTypes1 g (Let ds t)    = Let (map (fogTypes1 g) ds)
>                                    (fogTypes1 g t)
>     fogTypes1 g (Case t as)   = Case (fogTypes1 g t) (map (fogTypes1 g) as)
>     fogTypes1 g (t :? ty)     = fogTypes1 g t :? fogTy' g [] ty

>     renameTypes1 _ (TmVar x)     = TmVar x
>     renameTypes1 _ (TmCon c)     = TmCon c
>     renameTypes1 _ (TmInt k)     = TmInt k
>     renameTypes1 _ (CharLit c)   = CharLit c
>     renameTypes1 _ (StrLit s)    = StrLit s
>     renameTypes1 g (TmApp f s)   = TmApp (renameTypes1 g f) (renameTypes1 g s)
>     renameTypes1 g (TmBrace n)   = TmBrace (renameTy g n)
>     renameTypes1 g (Lam x b)     = Lam x (renameTypes1 g b)
>     renameTypes1 g (NumLam x b)  = NumLam x (renameTypes1 (wkRenaming g) b)
>     renameTypes1 g (Let ds t)    = Let (map (renameTypes1 g) ds)
>                                    (renameTypes1 g t)
>     renameTypes1 g (Case t as)   = Case (renameTypes1 g t) (map (renameTypes1 g) as)
>     renameTypes1 g (t :? ty)     = renameTypes1 g t :? renameTy g ty

> instance a ~ b => FV (Tm OK a) b where
>     fvFoldMap g (TmApp f s)   = fvFoldMap g f <.> fvFoldMap g s
>     fvFoldMap g (TmBrace n)   = fvFoldMap g n
>     fvFoldMap g (Lam _ b)     = fvFoldMap g b
>     fvFoldMap g (NumLam _ b)  = fvFoldMap (wkF g mempty) b 
>     fvFoldMap g (Let ds t)    = fvFoldMap g ds <.> fvFoldMap g t
>     fvFoldMap g (t :? ty)     = fvFoldMap g t <.> fvFoldMap g ty
>     fvFoldMap _ _             = mempty

> tmUnOp :: UnOp -> Tm s a -> Tm s a
> tmUnOp o m = TmVar (unOpString o) `TmApp` m

> tmBinOp :: BinOp -> Tm s a -> Tm s a -> Tm s a
> tmBinOp o m n = TmVar (binOpPrefixString o) `TmApp` m `TmApp` n

> tmComp :: Comparator -> Tm s a -> Tm s a -> Tm s a
> tmComp c m n = TmVar ("(" ++ compStringTm c ++ ")") `TmApp` m `TmApp` n



> data Decl s a where
>     FunDecl   :: TmName -> [Alt s a] -> Decl s a
>     SigDecl   :: TmName -> ATy s a KSet -> Decl s a

> deriving instance Show (Decl RAW a)
> deriving instance Show (Decl OK a)
> deriving instance Eq (Decl RAW a)

> instance TravTypes1 Decl where
>     travTypes1 g (FunDecl x ps) =
>         FunDecl x <$> traverse (travTypes1 g) ps
>     travTypes1 g (SigDecl x ty) = SigDecl x <$> g ty

>     fogTypes1 g (FunDecl x ps)  = FunDecl x (map (fogTypes1 g) ps)
>     fogTypes1 g (SigDecl x ty)  = SigDecl x (fogTy' g [] ty)

>     renameTypes1 g (FunDecl x ps)  = FunDecl x (map (renameTypes1 g) ps)
>     renameTypes1 g (SigDecl x ty)  = SigDecl x (renameTy g ty) 

> instance a ~ b => FV (Decl OK a) b where
>     fvFoldMap f (FunDecl _ as)       = fvFoldMap f as
>     fvFoldMap f (SigDecl _ t)        = fvFoldMap f t

> declName :: Decl s a -> String
> declName (FunDecl x _)       = x
> declName (SigDecl x _)       = x


> data Grd s a where
>     ExpGuard  :: [Tm s a] -> Grd s a
>     NumGuard  :: [Pred (ATy s a KNum)] -> Grd s a

> deriving instance Show (Grd RAW a)
> deriving instance Show (Grd OK a)
> deriving instance Eq (Grd RAW a)

> instance TravTypes1 Grd where

>     travTypes1 g (ExpGuard ts)  = ExpGuard <$> traverse (travTypes1 g) ts
>     travTypes1 g (NumGuard ps)  = NumGuard <$> traverse (traverse g) ps

>     fogTypes1 g (ExpGuard ts)  = ExpGuard (map (fogTypes1 g) ts)
>     fogTypes1 g (NumGuard ps)  = NumGuard (map (fmap (fogTy' g [])) ps)

>     renameTypes1 g (ExpGuard ts)  = ExpGuard (map (renameTypes1 g) ts)
>     renameTypes1 g (NumGuard ps)  = NumGuard (map (fmap (renameTy g)) ps)

> instance a ~ b => FV (Grd OK a) b where
>     fvFoldMap f (ExpGuard ts)  = fvFoldMap f ts
>     fvFoldMap f (NumGuard ps)  = fvFoldMap f ps







> data GrdTms s b where
>     Guarded    :: [(Grd :*: Tm) s b] -> [Decl s b] -> GrdTms s b
>     Unguarded  :: Tm s b -> [Decl s b] -> GrdTms s b

> deriving instance Show (GrdTms RAW a)
> deriving instance Show (GrdTms OK b)

> instance Eq (GrdTms RAW b) where
>     Guarded xs ds   == Guarded xs' ds'   = xs == xs' && ds == ds'
>     Unguarded t ds  == Unguarded t' ds'  = t == t' && ds == ds'
>     _               == _                 = False

> instance TravTypes1 GrdTms where
>     travTypes1 g (Guarded xs ds)     = Guarded <$> traverse (travTypes1 g) xs
>                                           <*> traverse (travTypes1 g) ds
>     travTypes1 g (Unguarded t ds)    = Unguarded <$> travTypes1 g t
>                                           <*> traverse (travTypes1 g) ds
>     fogTypes1 g (Guarded xs ds)      = Guarded (map (fogTypes1 g) xs)
>                                           (map (fogTypes1 g) ds)
>     fogTypes1 g (Unguarded t ds)     = Unguarded (fogTypes1 g t)
>                                           (map (fogTypes1 g) ds)
>     renameTypes1 g (Guarded xs ds)   = Guarded (map (renameTypes1 g) xs)
>                                           (map (renameTypes1 g) ds)
>     renameTypes1 g (Unguarded t ds)  = Unguarded (renameTypes1 g t)
>                                           (map (renameTypes1 g) ds)

> instance FV (GrdTms OK b) b where
>     fvFoldMap f (Guarded xs ds)   = fvFoldMap f xs <.> fvFoldMap f ds
>     fvFoldMap f (Unguarded t ds)  = fvFoldMap f t <.> fvFoldMap f ds

> data Alt s a where
>     Alt :: PatList s a b -> GrdTms s b -> Alt s a

> deriving instance Show (Alt RAW a)
> deriving instance Show (Alt OK a)

> instance Eq (Alt RAW a) where
>    (Alt xs gt) == (Alt xs' gt') =
>        hetEq xs xs' (gt == gt') False

> instance TravTypes1 Alt where
>     travTypes1 g (Alt xs gt) = Alt xs <$> travTypes1 g gt

>     fogTypes1 g (Alt xs gt) = Alt xs' (fogTypes1 g' gt)
>       where (xs', g') = fogTypes2 g xs

>     renameTypes1 g (Alt xs gt) = ext xs $ \ ex -> 
>       renameTypes2 g ex xs $ \ ex' xs' ->
>         Alt xs' (renameTypes1 (extRenaming ex ex' g) gt)

> instance a ~ b => FV (Alt OK a) b where
>     fvFoldMap f (Alt xs gt) = let (m, f') = fvFoldMap2 f xs
>                               in m <.> fvFoldMap f' gt

> isVarAlt :: Alt s a -> Bool
> isVarAlt (Alt P0 (Unguarded _ _))  = True
> isVarAlt _                         = False



> data CaseAlt s a where
>     CaseAlt :: Pat s a b -> GrdTms s b -> CaseAlt s a

> deriving instance Show (CaseAlt RAW a)
> deriving instance Show (CaseAlt OK a)

> instance Eq (CaseAlt RAW a) where
>    (CaseAlt x gt) == (CaseAlt x' gt') =
>        hetEq x x' (gt == gt') False

> instance TravTypes1 CaseAlt where

>     travTypes1 g (CaseAlt x gt) =  CaseAlt x <$> travTypes1 g gt

>     fogTypes1 g (CaseAlt x gt) = CaseAlt x' (fogTypes1 g' gt)
>         where (x', g') = fogTypes2 g x

>     renameTypes1 g (CaseAlt x gt) = ext x $ \ ex -> 
>       renameTypes2 g ex x $ \ ex' x' ->
>         CaseAlt x' (renameTypes1 (extRenaming ex ex' g) gt)

> instance a ~ b => FV (CaseAlt OK a) b where
>     fvFoldMap f (CaseAlt x gt) = let (m, f') = fvFoldMap2 f x
>                                  in m <.> fvFoldMap f' gt







> data RTC f s a b where
>     P0    :: RTC f s a a
>     (:!)  :: f s a b -> RTC f s b c -> RTC f s a c

> type PatList = RTC Pat

> deriving instance Show (RTC Pat s a b)

> infixr 5 :!

> instance HetEq (RTC Pat RAW a) where
>     hetEq P0         P0         t _ = t
>     hetEq (x :! xs)  (y :! ys)  t f = hetEq x y (hetEq xs ys t f) f
>     hetEq _          _          _ f = f

> instance TravTypes2 f => TravTypes2 (RTC f) where
>     fogTypes2 g P0         = (P0, g)
>     fogTypes2 g (p :! ps)  = (p' :! ps', g'')
>       where  (p', g')    = fogTypes2 g p
>              (ps', g'')  = fogTypes2 g' ps

>     renameTypes2 _ VS0 P0 q         = q VS0 P0
>     renameTypes2 g _ (p :! ps) q  = ext p $ \ eab ->
>       ext ps $ \ ebc ->
>         renameTypes2 g eab p $ \ eab' p' ->
>             renameTypes2 (extRenaming eab eab' g) ebc ps $ \ ebc' ps' ->
>                 extComp eab' ebc' $ \ eac' ->
>                     q (unsafeCoerce eac') (p' :! ps')
>     renameTypes2 _ (_ :<< _) P0 _ = error "renameTypes2: impossible"

>     ext P0         q = q VS0
>     ext (p :! ps)  q = ext p $ \ ex ->
>                               ext ps $ \ ex' ->
>                                   extComp ex ex' q


> instance FV2 f => FV2 (RTC f) where
>     fvFoldMap2 f P0 = (mempty, f)
>     fvFoldMap2 f (p :! ps) = let (m, f') = fvFoldMap2 f p
>                                  (m', f'') = fvFoldMap2 f' ps
>                              in (m <.> m', f'')

> rtcLength :: RTC f s a b -> Int
> rtcLength P0 = 0
> rtcLength (_ :! ps) = 1 + rtcLength ps

> patLength :: PatList s a b -> Int
> patLength = rtcLength

> data Pat s a b where
>     PatVar     :: TmName                      ->  Pat s a a
>     PatCon     :: TmConName -> PatList s a b  ->  Pat s a b
>     PatIgnore  ::                                 Pat s a a
>     PatBrace   :: String -> Integer           ->  Pat s a (a, KNum)
>     PatBraceK  :: Integer                     ->  Pat s a a
>     PatIntLit  :: Integer                     ->  Pat s a a
>     PatCharLit :: Char                        ->  Pat s a a
>     PatStrLit  :: String                      ->  Pat s a a
>     PatNPlusK  :: String -> Integer           ->  Pat s a a

> deriving instance Show (Pat s a b)

> instance HetEq (Pat RAW a) where
>     hetEq (PatVar x)       (PatVar y)         t _  | x == y  = t
>     hetEq (PatCon c xs)    (PatCon d ys)      t f  | c == d  = hetEq xs ys t f
>     hetEq PatIgnore        PatIgnore          t _  = t
>     hetEq (PatBrace _ j)   (PatBrace _ k)     t _  | j == k  = t
>     hetEq (PatBraceK j)    (PatBraceK k)      t _  | j == k  = t
>     hetEq (PatIntLit i)    (PatIntLit j)      t _  | i == j  = t
>     hetEq (PatCharLit c)   (PatCharLit c')    t _  | c == c' = t
>     hetEq (PatStrLit s)    (PatStrLit s')     t _  | s == s' = t 
>     hetEq (PatNPlusK n k)  (PatNPlusK n' k')  t _  | n == n' && k == k' = t
>     hetEq _                _                  _ f  = f

> instance TravTypes2 Pat where
>     fogTypes2 g (PatVar x)      = (PatVar x, g)
>     fogTypes2 g (PatCon x ps)   = (PatCon x ps', g')
>       where (ps', g') = fogTypes2 g ps
>     fogTypes2 g PatIgnore       = (PatIgnore, g)
>     fogTypes2 g (PatBrace x k)  = (PatBrace x k, wkF g x)
>     fogTypes2 g (PatBraceK k)   = (PatBraceK k, g)
>     fogTypes2 g (PatIntLit i)   = (PatIntLit i, g)
>     fogTypes2 g (PatCharLit c)  = (PatCharLit c, g)
>     fogTypes2 g (PatStrLit s)   = (PatStrLit s, g)
>     fogTypes2 g (PatNPlusK n k) = (PatNPlusK n k, g)

>     renameTypes2 _ VS0      (PatVar x)      q = q VS0 (PatVar x)
>     renameTypes2 g vs       (PatCon x ps)   q = renameTypes2 g vs ps
>                                                     (\ vs' ps' -> q vs' (PatCon x ps'))
>     renameTypes2 _ VS0      PatIgnore       q = q VS0 PatIgnore
>     renameTypes2 g (VS0 :<< v)  (PatBrace x k)  q = q (VS0 :<< g v) (PatBrace x k)
>     renameTypes2 _ VS0      (PatBraceK k)   q = q VS0 (PatBraceK k)
>     renameTypes2 _ VS0      (PatIntLit i)   q = q VS0 (PatIntLit i)
>     renameTypes2 _ VS0      (PatCharLit c)  q = q VS0 (PatCharLit c)
>     renameTypes2 _ VS0      (PatStrLit s)   q = q VS0 (PatStrLit s)
>     renameTypes2 _ VS0      (PatNPlusK n k) q = q VS0 (PatNPlusK n k)
>     renameTypes2 _ _        _               _ = error "renameTypes2: impossible"

>     ext (PatVar _)      q = q VS0
>     ext (PatCon _ xs)   q = ext xs q
>     ext PatIgnore       q = q VS0
>     ext (PatBrace _ _)  q = q (VS0 :<< error "woona")
>     ext (PatBraceK _)   q = q VS0
>     ext (PatIntLit _)   q = q VS0
>     ext (PatCharLit _)  q = q VS0
>     ext (PatStrLit _)   q = q VS0
>     ext (PatNPlusK _ _) q = q VS0

> instance FV2 Pat where
>     fvFoldMap2 f (PatVar _)      = (mempty, f)
>     fvFoldMap2 f (PatCon _ ps)   = fvFoldMap2 f ps
>     fvFoldMap2 f PatIgnore       = (mempty, f)
>     fvFoldMap2 f (PatBrace _ _)  = (mempty, wkF f mempty)
>     fvFoldMap2 f (PatBraceK _)   = (mempty, f)
>     fvFoldMap2 f (PatIntLit _)   = (mempty, f)
>     fvFoldMap2 f (PatCharLit _)  = (mempty, f)
>     fvFoldMap2 f (PatStrLit _)   = (mempty, f)
>     fvFoldMap2 f (PatNPlusK _ _) = (mempty, f)

> data VarBinding s a b where
>     VB  :: AVar s a k -> AKind s k -> VarBinding s a (a, k)

> deriving instance Show (VarBinding RAW a b)
> deriving instance Show (VarBinding OK a b)

> instance TravTypes2 VarBinding where
>     fogTypes2 g (VB x k) = (VB (g x) (fogKind k), wkF g (g x))
>     renameTypes2 g (VS0 :<< v) (VB x k) q = q (VS0 :<< g v) (VB (g x) k)
>     renameTypes2 _ _ _ _ = error "renameTypes2: impossible" 
>     ext (VB v _) q = q (VS0 :<< v)

> instance FV2 VarBinding where
>     fvFoldMap2 f (VB _ _) = (mempty, wkF f mempty)

> instance Eq (VarBinding RAW a b) where
>     VB x k == VB y l = x == y && k == l


> type VarList = RTC VarBinding

> deriving instance Show (RTC VarBinding RAW a b)
> deriving instance Show (RTC VarBinding OK a b)

> instance Eq (RTC VarBinding RAW a b) where
>     P0         ==  P0         = True
>     (x :! xs)  ==  (y :! ys)  = x == rawCoerce2 y && xs == rawCoerce2 ys
>     _          ==  _          = False



> data TyK s a b where
>     TyK :: ATy s a k -> AKind s k -> TyK s a (a, k) 
> deriving instance Show (TyK RAW a b)
> deriving instance Show (TyK OK a b)

> instance TravTypes2 TyK where
>     fogTypes2 g (TyK t k) = (TyK (fogTy' g [] t) (fogKind k), wkF g undefined)
>     renameTypes2 g (VS0 :<< v) (TyK t k) q = q (VS0 :<< g v) (TyK (renameTy g t) k)
>     renameTypes2 _ _ _ _ = error "renameTypes2: invariant violated"
>     ext (TyK _ _) q = q (VS0 :<< error "woonk")

> instance Eq (TyK RAW a b) where
>     TyK t k == TyK t' k' = t == t' && k == k'

> type TyList = RTC TyK

> deriving instance Show (RTC TyK RAW a b)
> deriving instance Show (RTC TyK OK a b)

> instance Eq (RTC TyK RAW a b) where
>     P0         ==  P0         = True
>     (x :! xs)  ==  (y :! ys)  = x == rawCoerce2 y && xs == rawCoerce2 ys
>     _          ==  _          = False



> data VarKind s a where
>     VK :: AVar s a k -> AKind s k -> VarKind s a

> deriving instance Eq (VarKind RAW ())
> deriving instance Show (VarKind RAW ())
> deriving instance Show (VarKind OK ())

> instance FV (VarKind OK ()) () where
>     fvFoldMap f (VK v _) = f v

> instance TravTypes1 VarKind where
>     travTypes1 _ vk = pure vk
>     fogTypes1 g (VK v k) = VK (g v) (fogKind k)
>     renameTypes1 g (VK v k) = VK (g v) k
>                               
> allWrapVK :: [VarKind OK ()] -> Type k -> Type k
> allWrapVK [] t = t
> allWrapVK (VK v k : xs) t = Bind All (nameToString (varName v)) k
>                                      (bindTy v (allWrapVK xs t)) 


> applyVK :: (forall k . Kind k -> Type k) -> [VarKind OK ()] -> Kind k' -> Type k'
> applyVK f xs k' = help xs k'
>       where
>         help :: [VarKind OK ()] -> Kind l -> Type l
>         help [] l = f l
>         help (VK v k : xks) l = help xks (k :-> l) `TyApp` TyVar v