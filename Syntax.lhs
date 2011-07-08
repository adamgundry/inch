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
> import TyNum
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
> type PatternList      = PatList OK
> type Pattern          = Pat OK
> type Declaration      = Decl OK
> type Program          = Prog OK
> type Guard            = Grd OK

> type STerm             = Tm RAW
> type SConstructor      = Con RAW
> type SAlternative      = Alt RAW
> type SPatternList      = PatList RAW
> type SPattern          = Pat RAW
> type SDeclaration      = Decl RAW
> type SProgram          = Prog RAW
> type SGuard            = Grd RAW



> class TravTypes t where
>     -- travTypes :: Applicative f =>
>     --     (forall k. Type k -> f (Type k)) -> t OK -> f (t OK)
>     fogTypes :: (forall k. Var a k -> String) -> t OK a -> t RAW a
>     renameTypes :: (forall k . Var a k -> Var c k) -> t OK a -> t OK c

> class TravTypes2 t where
>     fogTypes2 :: (forall k . Var a k -> String) -> t OK a b ->
>                     (t RAW a b, (forall k . Var b k -> String))
>     renameTypes2 ::
>         (forall k . Var a k -> Var c k) -> t OK a b ->
>             (forall d . (forall k . Var b k -> Var d k) -> t OK c d -> x) ->
>                 x
>
>     rawCoerce2 :: t RAW a b -> t RAW c d
>     rawCoerce2 = unsafeCoerce

> {-
> mapTypes :: TravTypes t =>
>                 (forall k. Type k -> Type k) -> t OK -> t OK
> mapTypes g = unId . travTypes (Id . g)

> replaceTypes :: TravTypes t => Var () k -> Type k -> t OK -> t OK
> replaceTypes a t = mapTypes (replaceTy a t)

> elemTypes :: TravTypes t => Var () k -> t OK -> Bool
> elemTypes a t = getAny $ getConst $ travTypes (Const . Any . (a <?)) t
> -}

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
>     TmBrace  :: TyNum (AVar s a KNum)     -> Tm s a
>     Lam      :: TmName -> Tm s a          -> Tm s a
>     NumLam   :: String -> Tm s (a, KNum)  -> Tm s a
>     Let      :: [Decl s a] -> Tm s a      -> Tm s a
>     (:?)     :: Tm s a -> ATy s a KSet    -> Tm s a

> deriving instance Eq (Tm RAW a)

> instance TravTypes Tm where

<     travTypes g (TmApp f s)  = TmApp <$> travTypes g f <*> travTypes g s
<     travTypes g (TmBrace n)  = TmBrace . toNum <$> g (TyNum n)
<     travTypes g (Lam x b)    = Lam x <$> travTypes g b
<     travTypes g (NumLam a b) = NumLam 
<     travTypes g (Let ds t)   = Let <$> traverse (travTypes g) ds
<                                    <*> travTypes g t
<     travTypes g (t :? ty)    = (:?) <$> travTypes g t <*> g ty
<     travTypes g t            = pure t

>     fogTypes g (TmVar x)     = TmVar x
>     fogTypes g (TmCon c)     = TmCon c
>     fogTypes g (TmInt k)     = TmInt k
>     fogTypes g (TmApp f s)   = TmApp (fogTypes g f) (fogTypes g s)
>     fogTypes g (TmBrace n)   = TmBrace (fogTyNum' g n)
>     fogTypes g (Lam x b)     = Lam x (fogTypes g b)
>     fogTypes g (NumLam x b)  = NumLam x (fogTypes (wkF g x) b)
>     fogTypes g (Let ds t)    = Let (map (fogTypes g) ds)
>                                    (fogTypes g t)
>     fogTypes g (t :? ty)     = fogTypes g t :? fogTy' g [] ty

>     renameTypes g (TmVar x)     = TmVar x
>     renameTypes g (TmCon c)     = TmCon c
>     renameTypes g (TmInt k)     = TmInt k
>     renameTypes g (TmApp f s)   = TmApp (renameTypes g f) (renameTypes g s)
>     renameTypes g (TmBrace n)   = TmBrace (fmap g n)
>     renameTypes g (Lam x b)     = Lam x (renameTypes g b)
>     renameTypes g (NumLam x b)  = NumLam x (renameTypes (wkRenaming g) b)
>     renameTypes g (Let ds t)    = Let (map (renameTypes g) ds)
>                                    (renameTypes g t)
>     renameTypes g (t :? ty)     = renameTypes g t :? renameTy g ty


> data Decl s a where
>     DataDecl  :: TyConName -> AKind s k -> [TmConName ::: ATy s a KSet] ->
>                      Decl s a
>     FunDecl   :: TmName -> [Alt s a] -> Decl s a
>     SigDecl   :: TmName -> ATy s a KSet -> Decl s a

> deriving instance Eq (Decl RAW a)

> instance TravTypes Decl where

<     travTypes g (DataDecl x k cs) =
<         DataDecl x k <$> traverse (\ (x ::: t) -> (x :::) <$> g t) cs
<     travTypes g (FunDecl x ps) =
<         FunDecl x <$> traverse (travTypes g) ps
<     travTypes g (SigDecl x ty) = SigDecl x <$> g ty

>     fogTypes g (DataDecl x k cs) = DataDecl x (fogKind k)
>         (map (\ (x ::: t) -> x ::: fogTy' g [] t) cs)
>     fogTypes g (FunDecl x ps)  = FunDecl x (map (fogTypes g) ps)
>     fogTypes g (SigDecl x ty)  = SigDecl x (fogTy' g [] ty)

>     renameTypes g (DataDecl x k cs) = DataDecl x k
>         (map (\ (x ::: t) -> x ::: renameTy g t) cs)
>     renameTypes g (FunDecl x ps)  = FunDecl x (map (renameTypes g) ps)
>     renameTypes g (SigDecl x ty)  = SigDecl x (renameTy g ty) 





> data Alt s a where
>     Alt :: PatList s a b -> Maybe (Grd s b) -> Tm s b -> Alt s a

> instance Eq (Alt RAW a) where
>    (Alt xs mg t) == (Alt xs' mg' t') =
>        hetEq xs xs' (mg == mg' && t == t') False

> instance TravTypes Alt where

<     travTypes g (Alt xs ms t) = 
<         Alt <$> traverse (travTypes g) xs
<             <*> traverse (travTypes g) ms
<             <*> travTypes g t

>     fogTypes g (Alt xs ms t) = 
>         Alt xs'
>             (fmap (fogTypes g') ms)
>             (fogTypes g' t)
>       where (xs', g') = fogTypes2 g xs

>     renameTypes g (Alt xs ms t) = renameTypes2 g xs (\ g' xs' ->
>         Alt xs'
>             (fmap (renameTypes g') ms)
>             (renameTypes g' t))



> isVarAlt :: Alt s a -> Bool
> isVarAlt (Alt P0 Nothing _)  = True
> isVarAlt _                   = False


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

>     renameTypes2 g P0 q         = q g P0
>     renameTypes2 g (p :! ps) q  = renameTypes2 g p (\ g' p' ->
>                                     renameTypes2 g' ps (\ g'' ps' ->
>                                         q g'' (p' :! ps')))

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

<     travTypes g t = pure t -- change me

>     fogTypes2 g (PatVar x)      = (PatVar x, g)
>     fogTypes2 g (PatCon x ps)   = (PatCon x ps', g')
>       where (ps', g') = fogTypes2 g ps
>     fogTypes2 g PatIgnore       = (PatIgnore, g)
>     fogTypes2 g (PatBrace x k)  = (PatBrace x k, wkF g x)
>     fogTypes2 g (PatBraceK k)   = (PatBraceK k, g)

>     renameTypes2 g (PatVar x)      q = q g (PatVar x)
>     renameTypes2 g (PatCon x ps)   q = renameTypes2 g ps
>                                            (\ g' ps' -> q g' (PatCon x ps'))
>     renameTypes2 g PatIgnore       q = q g PatIgnore
>     renameTypes2 g (PatBrace x k)  q = q (wkRenaming g) (PatBrace x k)
>     renameTypes2 g (PatBraceK k)   q = q g (PatBraceK k)


> data Grd s a where
>     ExpGuard  :: Tm s a -> Grd s a
>     NumGuard  :: [Pred (AVar s a KNum)] -> Grd s a

> deriving instance Eq (Grd RAW a)

> instance TravTypes Grd where

<     travTypes g (ExpGuard t)   = ExpGuard <$> travTypes g t
<     travTypes g (NumGuard ps)  = NumGuard <$> traverse (travPred gn) ps
<       where gn = (toNum <$>) . g . TyNum

>     fogTypes g (ExpGuard t)  = ExpGuard (fogTypes g t)
>     fogTypes g (NumGuard ps) = NumGuard (map (fogPred' g) ps)

>     renameTypes g (ExpGuard t)  = ExpGuard (renameTypes g t)
>     renameTypes g (NumGuard ps) = NumGuard (map (fmap g) ps)
