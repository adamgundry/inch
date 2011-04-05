> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
>              GADTs, TypeOperators, FlexibleInstances,
>              StandaloneDeriving, TypeFamilies, RankNTypes #-}

> module Syntax where

> import Control.Applicative
> import Control.Monad
> import Data.Foldable hiding (foldl1)
> import Data.Traversable

> import Kit
> import Kind
> import TyNum
> import Type


> data OK
> data RAW

> type family AKind k s
> type instance AKind k OK   = Kind k
> type instance AKind k RAW  = SKind

> type family ATy a k s
> type instance ATy a k OK   = Ty a k
> type instance ATy a k RAW  = SType

> type AType k s = ATy () k s

> type family AVar k s
> type instance AVar k OK   = Var () k
> type instance AVar k RAW  = String





> type Prog s       = [Decl s]
> type Con s        = TmConName ::: ATy () KSet s

> type Term             = Tm OK
> type Constructor      = Con OK
> type Pattern          = Pat OK
> type PatternTerm      = PatTerm OK
> type Declaration      = Decl OK
> type DataDeclaration  = DataDecl OK
> type FunDeclaration   = FunDecl OK
> type Program          = Prog OK
> type Guard            = Grd OK

> type STerm             = Tm RAW
> type SConstructor      = Con RAW
> type SPattern          = Pat RAW
> type SPatternTerm      = PatTerm RAW
> type SDeclaration      = Decl RAW
> type SDataDeclaration  = DataDecl RAW
> type SFunDeclaration   = FunDecl RAW
> type SProgram          = Prog RAW
> type SGuard            = Grd RAW


> class Fog t where
>     fog :: t OK -> t RAW

> class TravTypes t where
>     travTypes :: Applicative f =>
>                      (forall k. Type k -> f (Type k)) -> t -> f t


> data Tm s where
>     TmVar    :: TmName                -> Tm s
>     TmCon    :: TmConName             -> Tm s
>     TmInt    :: Integer               -> Tm s
>     TmApp    :: Tm s -> Tm s          -> Tm s
>     TmBrace  :: TyNum (AVar KNum s)   -> Tm s
>     Lam      :: TmName -> Tm s        -> Tm s
>     Let      :: [FunDecl s] -> Tm s   -> Tm s
>     (:?)     :: Tm s -> AType KSet s  -> Tm s

> deriving instance Eq (Tm RAW)

> instance Fog Tm where
>     fog (TmVar x)    = TmVar x
>     fog (TmCon c)    = TmCon c
>     fog (TmInt k)    = TmInt k
>     fog (TmApp f s)  = TmApp (fog f) (fog s)
>     fog (TmBrace n)  = TmBrace (fogTyNum n)
>     fog (Lam x b)    = Lam x (fog b)
>     fog (Let ds t)   = Let (map fog ds) (fog t)
>     fog (t :? ty)    = fog t :? fogTy ty

> instance TravTypes (Tm OK) where
>     travTypes g (TmApp f s)  = TmApp <$> travTypes g f <*> travTypes g s
>     travTypes g (TmBrace n)  = TmBrace . toNum <$> g (TyNum n)
>     travTypes g (Lam x b)    = Lam x <$> travTypes g b
>     travTypes g (Let ds t)   = Let <$> traverse (travTypes g) ds
>                                    <*> travTypes g t
>     travTypes g (t :? ty)    = (:?) <$> travTypes g t <*> g ty
>     travTypes g t = pure t


> data DataDecl s where
>     DataDecl  :: TyConName -> AKind k s -> [TmConName ::: AType KSet s] ->
>                      DataDecl s

> deriving instance Eq (DataDecl RAW)

> instance Fog DataDecl where
>     fog (DataDecl x k cs) = DataDecl x (fogKind k)
>         (map (\ (y ::: ty) -> y ::: fogTy ty) cs)

> instance TravTypes (DataDecl OK) where
>     travTypes g (DataDecl x k cs) =
>         DataDecl x k <$> traverse (travTypes g) cs


> data FunDecl s where
>     FunDecl   :: TmName -> Maybe (AType KSet s) -> [Pat s] -> FunDecl s

> deriving instance Eq (FunDecl RAW)

> instance Fog FunDecl where
>     fog (FunDecl x mt ps) = FunDecl x (fmap fogTy mt) (map fog ps)

> instance TravTypes (FunDecl OK) where
>     travTypes g (FunDecl x mt ps) =
>         FunDecl x <$> traverse g mt <*> traverse (travTypes g) ps

> data Decl s where
>     DD :: DataDecl s  -> Decl s
>     FD :: FunDecl s   -> Decl s

> deriving instance Eq (Decl RAW)

> instance Fog Decl where
>     fog (DD d) = DD (fog d)
>     fog (FD f) = FD (fog f)

> instance TravTypes (Decl OK) where
>     travTypes g (DD d) = DD <$> travTypes g d
>     travTypes g (FD f) = FD <$> travTypes g f


> data Pat s where
>     Pat :: [PatTerm s] -> Maybe (Grd s) -> Tm s -> Pat s

> deriving instance Eq (Pat RAW)

> instance Fog Pat where
>     fog (Pat xs mg t) = Pat (map fog xs) (fmap fog mg) (fog t)

> instance TravTypes (Pat OK) where
>     travTypes g (Pat xs ms t) = 
>         Pat <$> traverse (travTypes g) xs
>             <*> traverse (travTypes g) ms
>             <*> travTypes g t


> data PatTerm s where
>     PatVar     :: TmName -> PatTerm s
>     PatCon     :: TmConName -> [PatTerm s] -> PatTerm s
>     PatIgnore  :: PatTerm s
>     PatBrace   :: Maybe TmName -> Integer -> PatTerm s

> deriving instance Eq (PatTerm RAW)

> instance Fog PatTerm where
>     fog (PatVar x)       = PatVar x
>     fog (PatCon x ps)    = PatCon x (map fog ps)
>     fog PatIgnore        = PatIgnore
>     fog (PatBrace mt k)  = PatBrace mt k

> instance TravTypes (PatTerm OK) where
>     travTypes g t = pure t -- change if types added to pattern terms


> data Grd s where
>     ExpGuard  :: Tm s -> Grd s
>     NumGuard  :: [Pred (AVar KNum s)] -> Grd s

> deriving instance Eq (Grd RAW)

> instance Fog Grd where
>     fog (ExpGuard t)   = ExpGuard (fog t)
>     fog (NumGuard ps)  = NumGuard (map fogPred ps)

> instance TravTypes (Grd OK) where
>     travTypes g (ExpGuard t) = pure $ ExpGuard t
>     travTypes g (NumGuard ps) = NumGuard <$> traverse (travPred gn) ps
>       where gn = (toNum <$>) . g . TyNum



> instance TravTypes (TmConName ::: Type k) where
>     travTypes g (x ::: t) = (x :::) <$> g t


> partitionDecls :: [Decl s] -> ([DataDecl s], [FunDecl s])
> partitionDecls [] = ([], [])
> partitionDecls (DD d : xs) = (d:ds, fs)
>   where (ds, fs) = partitionDecls xs
> partitionDecls (FD f : xs) = (ds, f:fs)
>   where (ds, fs) = partitionDecls xs






> {-
 
> subsTy :: Applicative f =>
>     (a -> f (TyNum b)) ->
>     (k -> a -> f (Ty k b)) ->
>     Ty k a -> f (Ty k b)
> subsTy fn fa (TyVar k a)     = fa k a
> subsTy fn fa (TyCon c)       = pure $ TyCon c
> subsTy fn fa (TyApp f s)     = TyApp <$> subsTy fn fa f <*> subsTy fn fa s
> --subsTy fn fa (TyB b)         = pure $ TyB b
> subsTy fn fa (TyNum n)       = TyNum <$> subsTyNum fn n
> subsTy fn fa (Bind b x k t)  = Bind b x k <$> subsTy (wkwk NumVar fn) fa' t
>   where
>     fa' k Z      = pure $ TyVar k Z
>     fa' k (S a)  = fmap S <$> fa k a
> subsTy fn fa (Qual p t)      = Qual <$> subsPred fn p <*> subsTy fn fa t


> travTy :: Applicative f =>
>     (a -> f b) ->
>     (k -> a -> f b) ->
>     Ty k a -> f (Ty k b)
> travTy fn fa = subsTy ((NumVar <$>) . fn) (\ k a -> TyVar k <$> fa k a)

> travTyNum :: Applicative f =>
>     (a -> f b) ->
>     TyNum a -> f (TyNum b)
> travTyNum fn = subsTyNum ((NumVar <$>) . fn)



> instance Trav3 Tm where
>     trav3 fn fa fx (TmVar x)    = TmVar <$> fx x
>     trav3 fn fa fx (TmCon c)    = pure $ TmCon c
>     trav3 fn fa fx (TmInt k)    = pure $ TmInt k
>     trav3 fn fa fx (TmApp f s)  = TmApp <$> trav3 fn fa fx f <*> trav3 fn fa fx s
>     trav3 fn fa fx (TmBrace n)  = TmBrace <$> fn n
>     trav3 fn fa fx (Lam x t)    = Lam x <$> trav3 fn fa (wk fx) t
>     trav3 fn fa fx (Let ds t)   = Let <$> traverse (trav3 fn fa fx) ds
>                                       <*> trav3 fn fa fx t
>     trav3 fn fa fx (t :? ty)    = (:?) <$> trav3 fn fa fx t <*> fa ty

> instance Trav3 DataDecl where
>     trav3 fn fa fx (DataDecl x k cs) =
>         DataDecl x k <$> traverse (traverse fa) cs

> instance Trav3 FunDecl where
>     trav3 fn fa fx (FunDecl x mt ps) =
>         FunDecl <$> fx x <*> traverse fa mt
>                          <*> traverse (trav3 fn fa fx) ps

> instance Trav3 Decl where
>     trav3 fn fa fx (DD d) = DD <$> trav3 fn fa fx d
>     trav3 fn fa fx (FD d) = FD <$> trav3 fn fa fx d

> instance Trav3 Pat where
>     trav3 fn fa fx (Pat pts r t) =
>         Pat <$> traverse (trav3 fn fa fx) pts
>             <*> traverse (trav3 fn fa fx) r
>             <*> trav3 fn fa fx t

> instance Trav3 PatTerm where
>     trav3 fn fa fx (PatVar x)       = PatVar <$> fx x
>     trav3 fn fa fx (PatCon c pts)   = PatCon c <$> traverse (trav3 fn fa fx) pts
>     trav3 fn fa fx PatIgnore        = pure PatIgnore
>     trav3 fn fa fx (PatBrace mx k)  = PatBrace <$> traverse fx mx <*> pure k

> instance Trav3 Grd where
>     trav3 fn fa fx (ExpGuard t)   = ExpGuard <$> trav3 fn fa fx t
>     trav3 fn fa fx (NumGuard ps)  = NumGuard <$> traverse (travPred fn) ps


> bindTy :: (a -> TyNum b) -> (k -> a -> Ty k b) -> Ty k a -> Ty k b
> bindTy fn fa = unId . subsTy (Id . fn) ((Id .) . fa)



> bind3 :: (Ord a, Ord b, Trav3 t) => (a -> TyNum b) -> (k -> a -> Ty k b) -> (x -> y) -> t k a x -> t k b y
> bind3 fn fa fx = unId . trav3 (subsTyNum (Id . fn)) (subsTy (Id . fn) ((Id .) . fa)) (Id . fx)


> bimap :: (Ord a, Ord b, Trav3 t) => (a -> b) -> (x -> y) -> t k a x -> t k b y
> bimap fa fx = bind3 (NumVar . fa) (\ k a -> TyVar k (fa a)) fx

> mangle :: (Ord a, Ord b, Trav3 t) => (TyNum a -> TyNum b) ->
>                 (Ty k a -> Ty l b) -> (x -> y) ->
>                 t k a x -> t l b y
> mangle fn fa fx = unId . trav3 (Id . fn) (Id . fa) (Id . fx)

> -}

> {-


> replaceTyNum :: Eq a => a -> TyNum a -> TyNum a -> TyNum a
> replaceTyNum a n = (>>= f)
>   where f b | a == b     = n
>             | otherwise  = NumVar b

> replace3 :: (Ord a, Trav3 t) => Kind -> a -> Ty Kind a -> t Kind a x -> t Kind a x
> replace3 KindNum a t  = mangle (replaceTyNum a (toNum t)) (replaceTy KindNum a t) id
> replace3 k a t        = mangle id (replaceTy k a t) id

> -}



> mapTypes :: TravTypes t => (forall k. Type k -> Type k) -> t -> t
> mapTypes g = unId . travTypes (Id . g)

> replaceTypes :: TravTypes t => Var () k -> Type k -> t -> t
> replaceTypes a t = mapTypes (replaceTy a t)