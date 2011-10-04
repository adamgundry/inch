> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
>              GADTs, TypeOperators, FlexibleInstances,
>              StandaloneDeriving, TypeFamilies, RankNTypes,
>              ImpredicativeTypes #-}

> module Syntax where

> import Control.Applicative
> import Control.Monad
> import Data.Foldable hiding (foldl1)
> import Data.Traversable
> import Data.Monoid
> import Unsafe.Coerce

> import Kit
> import Kind
> import Type


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





> type Prog s       = [Decl s ()]
> type Con s        = TmConName ::: ATy s () KSet

> type Term             = Tm OK
> type Constructor      = Con OK
> type Alternative      = Alt OK
> type CaseAlternative  = CaseAlt OK
> type PatternList      = PatList OK
> type Pattern          = Pat OK
> type Declaration      = Decl OK
> type Program          = Prog OK
> type Guard            = Grd OK

> type STerm             = Tm RAW
> type SConstructor      = Con RAW
> type SAlternative      = Alt RAW
> type SCaseAlternative  = CaseAlt RAW
> type SPatternList      = PatList RAW
> type SPattern          = Pat RAW
> type SDeclaration      = Decl RAW
> type SProgram          = Prog RAW
> type SGuard            = Grd RAW



> class TravTypes t where
>     travTypes :: Applicative f =>
>          (forall a k . Ty a k -> f (Ty a k)) -> t OK b -> f (t OK b)
>     fogTypes :: (forall k. Var a k -> String) -> t OK a -> t RAW a
>     renameTypes :: (forall k . Var a k -> Var c k) -> t OK a -> t OK c
>     rawCoerce :: t RAW a -> t RAW c
>     rawCoerce = unsafeCoerce

> mapTypes :: TravTypes t =>
>                 (forall a k. Ty a k -> Ty a k) -> t OK b -> t OK b
> mapTypes g = unId . travTypes (Id . g)

> replaceTypes :: TravTypes t => Var () k -> Type k -> t OK a -> t OK a
> replaceTypes a t = mapTypes (replaceTy (wkClosedVar a) (wkClosedTy t))

> elemsTypes :: TravTypes t => [Var () k] -> t OK a -> Bool
> elemsTypes as t = getAny $ getConst $ travTypes (Const . Any . (as <<?)) t

> elemTypes :: TravTypes t => Var () k -> t OK a -> Bool
> elemTypes a t = elemsTypes [a] t

> bindTm v = renameTypes (bindVar v)
> unbindTm v = renameTypes (unbindVar v)

> fog :: TravTypes t => t OK () -> t RAW ()
> fog = fogTypes fogVar

> fogSys :: TravTypes t => t OK () -> t RAW ()
> fogSys = fogTypes fogSysVar

> fogSys2 :: TravTypes2 t => t OK () a -> t RAW () a
> fogSys2 = fst . fogTypes2 fogSysVar


> data Tm s a where
>     TmVar    :: TmName                    -> Tm s a
>     TmCon    :: TmConName                 -> Tm s a
>     TmInt    :: Integer                   -> Tm s a
>     TmApp    :: Tm s a -> Tm s a          -> Tm s a
>     TmBrace  :: ATy s a KNum              -> Tm s a
>     Lam      :: TmName -> Tm s a          -> Tm s a
>     NumLam   :: String -> Tm s (a, KNum)  -> Tm s a
>     Let      :: [Decl s a] -> Tm s a      -> Tm s a
>     Case     :: Tm s a -> [CaseAlt s a]   -> Tm s a
>     (:?)     :: Tm s a -> ATy s a KSet    -> Tm s a

> deriving instance Eq (Tm RAW a)

> instance TravTypes Tm where

>     travTypes g (TmApp f s)  = TmApp <$> travTypes g f <*> travTypes g s
>     travTypes g (TmBrace n)  = TmBrace <$> g n
>     travTypes g (Lam x b)    = Lam x <$> travTypes g b
>     travTypes g (NumLam a b) = NumLam a <$> travTypes g b 
>     travTypes g (Let ds t)   = Let <$> traverse (travTypes g) ds
>                                    <*> travTypes g t
>     travTypes g (t :? ty)    = (:?) <$> travTypes g t <*> g ty
>     travTypes g t            = pure t

>     fogTypes g (TmVar x)     = TmVar x
>     fogTypes g (TmCon c)     = TmCon c
>     fogTypes g (TmInt k)     = TmInt k
>     fogTypes g (TmApp f s)   = TmApp (fogTypes g f) (fogTypes g s)
>     fogTypes g (TmBrace n)   = TmBrace (fogTy' g [] n)
>     fogTypes g (Lam x b)     = Lam x (fogTypes g b)
>     fogTypes g (NumLam x b)  = NumLam x (fogTypes (wkF g x) b)
>     fogTypes g (Let ds t)    = Let (map (fogTypes g) ds)
>                                    (fogTypes g t)
>     fogTypes g (Case t as)   = Case (fogTypes g t) (map (fogTypes g) as)
>     fogTypes g (t :? ty)     = fogTypes g t :? fogTy' g [] ty

>     renameTypes g (TmVar x)     = TmVar x
>     renameTypes g (TmCon c)     = TmCon c
>     renameTypes g (TmInt k)     = TmInt k
>     renameTypes g (TmApp f s)   = TmApp (renameTypes g f) (renameTypes g s)
>     renameTypes g (TmBrace n)   = TmBrace (renameTy g n)
>     renameTypes g (Lam x b)     = Lam x (renameTypes g b)
>     renameTypes g (NumLam x b)  = NumLam x (renameTypes (wkRenaming g) b)
>     renameTypes g (Let ds t)    = Let (map (renameTypes g) ds)
>                                    (renameTypes g t)
>     renameTypes g (Case t as)   = Case (renameTypes g t) (map (renameTypes g) as)
>     renameTypes g (t :? ty)     = renameTypes g t :? renameTy g ty


> data Decl s a where
>     DataDecl  :: TyConName -> AKind s k -> [TmConName ::: ATy s a KSet] ->
>                      Decl s a
>     FunDecl   :: TmName -> [Alt s a] -> Decl s a
>     SigDecl   :: TmName -> ATy s a KSet -> Decl s a

> deriving instance Eq (Decl RAW a)

> instance TravTypes Decl where

>     travTypes g (DataDecl x k cs) =
>         DataDecl x k <$> traverse (\ (x ::: t) -> (x :::) <$> g t) cs
>     travTypes g (FunDecl x ps) =
>         FunDecl x <$> traverse (travTypes g) ps
>     travTypes g (SigDecl x ty) = SigDecl x <$> g ty

>     fogTypes g (DataDecl x k cs) = DataDecl x (fogKind k)
>         (map (\ (x ::: t) -> x ::: fogTy' g [] t) cs)
>     fogTypes g (FunDecl x ps)  = FunDecl x (map (fogTypes g) ps)
>     fogTypes g (SigDecl x ty)  = SigDecl x (fogTy' g [] ty)

>     renameTypes g (DataDecl x k cs) = DataDecl x k
>         (map (\ (x ::: t) -> x ::: renameTy g t) cs)
>     renameTypes g (FunDecl x ps)  = FunDecl x (map (renameTypes g) ps)
>     renameTypes g (SigDecl x ty)  = SigDecl x (renameTy g ty) 



> data Grd s a where
>     ExpGuard  :: Tm s a -> Grd s a
>     NumGuard  :: [Pred (ATy s a KNum)] -> Grd s a

> deriving instance Eq (Grd RAW a)

> instance TravTypes Grd where

>     travTypes g (ExpGuard t)   = ExpGuard <$> travTypes g t
>     travTypes g (NumGuard ps)  = NumGuard <$> traverse (traverse g) ps

>     fogTypes g (ExpGuard t)  = ExpGuard (fogTypes g t)
>     fogTypes g (NumGuard ps) = NumGuard (map (fmap (fogTy' g [])) ps)

>     renameTypes g (ExpGuard t)  = ExpGuard (renameTypes g t)
>     renameTypes g (NumGuard ps) = NumGuard (map (fmap (renameTy g)) ps)





> data Ext a b x where
>     E0  :: Ext a a ()
>     EC  :: Ext a b x -> Ext a (b, k) (x, k)

> extBVar :: Ext a b x -> BVar a k -> BVar b k
> extBVar E0       v = v
> extBVar (EC ex)  v = Pop (extBVar ex v)

> extVar :: Ext a b x -> Var a k -> Var b k
> extVar _   (FVar a k)  = FVar a k
> extVar ex  (BVar v)    = BVar (extBVar ex v)

> extRenaming :: Ext a b x -> Ext c d x -> (Var a k -> Var c k) ->
>                    Var b k -> Var d k
> extRenaming _         ecd       g (FVar a k)      = extVar ecd $ g (FVar a k)
> extRenaming E0        E0        g (BVar v)        = g (BVar v)
> extRenaming (EC _)    (EC _)    g (BVar Top)      = BVar Top
> extRenaming (EC eab)  (EC ecd)  g (BVar (Pop v))  = wkVar $ extRenaming eab ecd g (BVar v)

> extExt :: Ext a b x -> (forall d y . Ext c d y -> p) -> p
> extExt E0       q = q E0
> extExt (EC ex)  q = extExt ex (q . EC)

> extComp :: Ext a b x -> Ext b c y -> (forall z . Ext a c z -> p) -> p
> extComp eab E0        q = q eab
> extComp eab (EC ebc)  q = extComp eab ebc (q . EC)


> data Alt s a where
>     Alt :: PatList s a b -> Maybe (Grd s b) -> Tm s b -> Alt s a

> instance Eq (Alt RAW a) where
>    (Alt xs mg t) == (Alt xs' mg' t') =
>        hetEq xs xs' (mg == mg' && t == t') False

> instance TravTypes Alt where

>     travTypes g (Alt xs ms t) = 
>         Alt xs
>             <$> traverse (travTypes g) ms
>             <*> travTypes g t

>     fogTypes g (Alt xs ms t) = 
>         Alt xs'
>             (fmap (fogTypes g') ms)
>             (fogTypes g' t)
>       where (xs', g') = fogTypes2 g xs

>     renameTypes g (Alt xs ms t) = extPatList xs $ \ ex -> 
>       renameTypes2 g ex xs $ \ ex' xs' ->
>         Alt xs'
>             (fmap (renameTypes (extRenaming ex ex' g)) ms)
>             (renameTypes (extRenaming ex ex' g) t)

> instance FV (Alt OK a) where
>     (<<?) = elemsTypes

> isVarAlt :: Alt s a -> Bool
> isVarAlt (Alt P0 Nothing _)  = True
> isVarAlt _                   = False



> data CaseAlt s a where
>     CaseAlt :: Pat s a b -> Maybe (Grd s b) -> Tm s b -> CaseAlt s a

> instance Eq (CaseAlt RAW a) where
>    (CaseAlt x mg t) == (CaseAlt x' mg' t') =
>        hetEq x x' (mg == mg' && t == t') False

> instance TravTypes CaseAlt where

>     travTypes g (CaseAlt x ms t) = 
>         CaseAlt x
>             <$> traverse (travTypes g) ms
>             <*> travTypes g t

>     fogTypes g (CaseAlt x ms t) = 
>         CaseAlt x'
>             (fmap (fogTypes g') ms)
>             (fogTypes g' t)
>       where (x', g') = fogTypes2 g x

>     renameTypes g (CaseAlt x ms t) = extPat x $ \ ex -> 
>       renameTypes2 g ex x $ \ ex' x' ->
>         CaseAlt x'
>             (fmap (renameTypes (extRenaming ex ex' g)) ms)
>             (renameTypes (extRenaming ex ex' g) t)

> instance FV (CaseAlt OK a) where
>     (<<?) = elemsTypes




> class TravTypes2 t where
>     fogTypes2 :: (forall k . Var a k -> String) -> t OK a b ->
>                     (t RAW a b, (forall k . Var b k -> String))
>     renameTypes2 ::
>         (forall k . Var a k -> Var c k) -> Ext a b x -> t OK a b ->
>             (forall d . Ext c d x -> t OK c d -> p) ->
>                 p
>
>     rawCoerce2 :: t RAW a b -> t RAW c d
>     rawCoerce2 = unsafeCoerce


> bindUn :: TravTypes2 t =>
>             Var a k -> Ext a b x -> VarSuffix a b -> t OK a b ->
>              (forall d . Ext (a, k) d x -> VarSuffix a d ->
>                  t OK (a, k) d -> p) -> p
> bindUn v ex vs t q = renameTypes2 (bindVar v) ex t $ \ ex' t' -> q ex' (error "bindUn") t'



> data PatList s a b where
>     P0    :: PatList s a a
>     (:!)  :: Pat s a b -> PatList s b c -> PatList s a c

> infixr 5 :!

> instance HetEq (PatList RAW a) where
>     hetEq P0 P0 t f = t
>     hetEq (x :! xs) (y :! ys) t f = hetEq x y (hetEq xs ys t f) f
>     hetEq _ _ t f = f

> instance TravTypes2 PatList where
>     fogTypes2 g P0         = (P0, g)
>     fogTypes2 g (p :! ps)  = (p' :! ps', g'')
>       where  (p', g')    = fogTypes2 g p
>              (ps', g'')  = fogTypes2 g' ps

>     renameTypes2 g E0 P0 q         = q E0 P0
>     renameTypes2 g eac (p :! ps) q  = extPat p $ \ eab ->
>       extPatList ps $ \ ebc ->
>         renameTypes2 g eab p $ \ eab' p' ->
>             renameTypes2 (extRenaming eab eab' g) ebc ps $ \ ebc' ps' ->
>                 extComp eab' ebc' $ \ eac' ->
>                     q (unsafeCoerce eac') (p' :! ps')


> patLength :: PatList s a b -> Int
> patLength P0 = 0
> patLength (_ :! ps) = 1 + patLength ps


> data Pat s a b where
>     PatVar     :: TmName                      ->  Pat s a a
>     PatCon     :: TmConName -> PatList s a b  ->  Pat s a b
>     PatIgnore  ::                                 Pat s a a
>     PatBrace   :: String -> Integer           ->  Pat s a (a, KNum)
>     PatBraceK  :: Integer                     ->  Pat s a a

> instance HetEq (Pat RAW a) where
>     hetEq (PatVar x)      (PatVar y) t f      | x == y  = t
>     hetEq (PatCon c xs)   (PatCon d ys) t f   | c == d  = hetEq xs ys t f
>     hetEq PatIgnore       PatIgnore t f                 = t
>     hetEq (PatBrace _ j)  (PatBrace _ k) t f  | j == k  = t
>     hetEq (PatBraceK j)   (PatBraceK k) t f   | j == k  = t
>     hetEq _ _ _ f = f

> instance TravTypes2 Pat where
>     fogTypes2 g (PatVar x)      = (PatVar x, g)
>     fogTypes2 g (PatCon x ps)   = (PatCon x ps', g')
>       where (ps', g') = fogTypes2 g ps
>     fogTypes2 g PatIgnore       = (PatIgnore, g)
>     fogTypes2 g (PatBrace x k)  = (PatBrace x k, wkF g x)
>     fogTypes2 g (PatBraceK k)   = (PatBraceK k, g)

>     renameTypes2 g E0       (PatVar x)      q = q E0 (PatVar x)
>     renameTypes2 g ex       (PatCon x ps)   q = renameTypes2 g ex ps
>                                                     (\ ex' ps' -> q ex' (PatCon x ps'))
>     renameTypes2 g E0       PatIgnore       q = q E0 PatIgnore
>     renameTypes2 g (EC E0)  (PatBrace x k)  q = q (EC E0) (PatBrace x k)
>     renameTypes2 g E0       (PatBraceK k)   q = q E0 (PatBraceK k)

> extPat :: Pat s a b -> (forall x . Ext a b x -> p) -> p
> extPat (PatVar _)      q = q E0
> extPat (PatCon _ xs)   q = extPatList xs q
> extPat PatIgnore       q = q E0
> extPat (PatBrace _ _)  q = q (EC E0)
> extPat (PatBraceK _)   q = q E0

> extPatList :: PatList s a b -> (forall x . Ext a b x -> p) -> p
> extPatList P0         q = q E0
> extPatList (p :! ps)  q = extPat p $ \ ex ->
>                               extPatList ps $ \ ex' ->
>                                   extComp ex ex' q
