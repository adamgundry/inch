> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
>              GADTs, TypeOperators, FlexibleInstances #-}

> module Syntax where

> import Control.Applicative
> import Control.Monad
> import Data.Foldable hiding (foldl1)
> import Data.Traversable

> import Kit
> import Type
> import TyNum


> data Tm k a x where
>     TmVar    :: x -> Tm k a x
>     TmCon    :: TmConName -> Tm k a x
>     TmInt    :: Integer -> Tm k a x
>     TmApp    :: Tm k a x -> Tm k a x -> Tm k a x
>     TmBrace  :: TyNum a -> Tm k a x
>     Lam      :: String -> Tm k a (S x) -> Tm k a x
>     Let      :: [FunDecl k a x] -> Tm k a x -> Tm k a x
>     (:?)     :: Tm k a x -> Ty k a -> Tm k a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)


> data DataDecl k a x where
>     DataDecl  :: TyConName -> Kind -> [TmConName ::: Ty k a] -> DataDecl k a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data FunDecl k a x where
>     FunDecl   :: x -> Maybe (Ty k a) -> [Pat k a x] -> FunDecl k a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data Decl k a x where
>     DD :: DataDecl k a x  -> Decl k a x
>     FD :: FunDecl k a x   -> Decl k a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data Pat k a x where
>     Pat :: [PatTerm k a x] -> Grd k a x -> Tm k a x -> Pat k a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data PatTerm k a x where
>     PatVar     :: x -> PatTerm k a x
>     PatCon     :: TmConName -> [PatTerm k a x] -> PatTerm k a x
>     PatIgnore  :: PatTerm k a x
>     PatBrace   :: Maybe x -> Integer -> PatTerm k a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data Grd k a x where
>     NoGuard   :: Grd k a x
>     ExpGuard  :: Tm k a x -> Grd k a x
>     NumGuard  :: [Pred a] -> Grd k a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)



> partitionDecls :: [Decl k a x] -> ([DataDecl k a x], [FunDecl k a x])
> partitionDecls [] = ([], [])
> partitionDecls (DD d : xs) = (d:ds, fs)
>   where (ds, fs) = partitionDecls xs
> partitionDecls (FD f : xs) = (ds, f:fs)
>   where (ds, fs) = partitionDecls xs


> subsTyNum :: Applicative f =>
>     (a -> f (TyNum b)) ->
>     TyNum a -> f (TyNum b)
> subsTyNum fn (NumVar a)    = fn a
> subsTyNum fn (NumConst k)  = pure $ NumConst k
> subsTyNum fn (n :+: m)     = (:+:) <$> subsTyNum fn n <*> subsTyNum fn m
> subsTyNum fn (n :*: m)     = (:*:) <$> subsTyNum fn n <*> subsTyNum fn m
> subsTyNum fn (Neg n)       = Neg <$> subsTyNum fn n

> subsPred :: Applicative f =>
>     (a -> f (TyNum b)) ->
>     Pred a -> f (Pred b)
> subsPred fn (P c m n) = P c <$> subsTyNum fn m <*> subsTyNum fn n
 
> subsTy :: Applicative f =>
>     (a -> f (TyNum b)) ->
>     (k -> a -> f (Ty k b)) ->
>     Ty k a -> f (Ty k b)
> subsTy fn fa (TyVar k a)     = fa k a
> subsTy fn fa (TyCon c)       = pure $ TyCon c
> subsTy fn fa (TyApp f s)     = TyApp <$> subsTy fn fa f <*> subsTy fn fa s
> subsTy fn fa (TyB b)         = pure $ TyB b
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

> class Trav3 t where
>     trav3 :: (Ord a, Ord b, Applicative f) => (TyNum a -> f (TyNum b)) ->
>                 (Ty k a -> f (Ty l b)) -> (x -> f y) ->
>                 t k a x -> f (t l b y)

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
>         Pat <$> traverse (trav3 fn fa fx) pts <*> trav3 fn fa fx r
>                                               <*> trav3 fn fa fx t

> instance Trav3 PatTerm where
>     trav3 fn fa fx (PatVar x)       = PatVar <$> fx x
>     trav3 fn fa fx (PatCon c pts)   = PatCon c <$> traverse (trav3 fn fa fx) pts
>     trav3 fn fa fx PatIgnore        = pure PatIgnore
>     trav3 fn fa fx (PatBrace mx k)  = PatBrace <$> traverse fx mx <*> pure k

> instance Trav3 Grd where
>     trav3 fn fa fx NoGuard        = pure NoGuard
>     trav3 fn fa fx (ExpGuard t)   = ExpGuard <$> trav3 fn fa fx t
>     trav3 fn fa fx (NumGuard ps)  = NumGuard <$> traverse (travPred fn) ps


> bindTy :: (a -> TyNum b) -> (k -> a -> Ty k b) -> Ty k a -> Ty k b
> bindTy fn fa = unId . subsTy (Id . fn) ((Id .) . fa)

> bindPred :: (a -> TyNum b) -> Pred a -> Pred b
> bindPred f = unId . subsPred (Id . f)

> bind3 :: (Ord a, Ord b, Trav3 t) => (a -> TyNum b) -> (k -> a -> Ty k b) -> (x -> y) -> t k a x -> t k b y
> bind3 fn fa fx = unId . trav3 (subsTyNum (Id . fn)) (subsTy (Id . fn) ((Id .) . fa)) (Id . fx)


> bimap :: (Ord a, Ord b, Trav3 t) => (a -> b) -> (x -> y) -> t k a x -> t k b y
> bimap fa fx = bind3 (NumVar . fa) (\ k a -> TyVar k (fa a)) fx

> mangle :: (Ord a, Ord b, Trav3 t) => (TyNum a -> TyNum b) ->
>                 (Ty k a -> Ty l b) -> (x -> y) ->
>                 t k a x -> t l b y
> mangle fn fa fx = unId . trav3 (Id . fn) (Id . fa) (Id . fx)

> replaceTy :: Ord a => Kind -> a -> Ty Kind a -> Ty Kind a -> Ty Kind a
> replaceTy KindNum a t = bindTy f g
>   where  f b  | a == b          = t'
>               | otherwise       = NumVar b
>          g KindNum b | a == b   = t
>          g k b                  = TyVar k b
>          t'                     = toNum t
> replaceTy l a t = bindTy NumVar f
>   where f k b  | a == b     = t
>                | otherwise  = TyVar k b

> replaceTyNum :: Eq a => a -> TyNum a -> TyNum a -> TyNum a
> replaceTyNum a n = (>>= f)
>   where f b | a == b     = n
>             | otherwise  = NumVar b

> replace3 :: (Ord a, Trav3 t) => Kind -> a -> Ty Kind a -> t Kind a x -> t Kind a x
> replace3 KindNum a t  = mangle (replaceTyNum a (toNum t)) (replaceTy KindNum a t) id
> replace3 k a t        = mangle id (replaceTy k a t) id


> type Prog k a x       = [Decl k a x]
> type Con k a          = TmConName ::: Ty k a

> type Term             = Tm Kind TyName TmName
> type Constructor      = Con Kind TyName
> type Pattern          = Pat Kind TyName TmName
> type PatternTerm      = PatTerm Kind TyName TmName
> type Declaration      = Decl Kind TyName TmName
> type DataDeclaration  = DataDecl Kind TyName TmName
> type FunDeclaration   = FunDecl Kind TyName TmName
> type Program          = Prog Kind TyName TmName
> type Guard            = Grd Kind TyName TmName

> type STerm             = Tm () String String
> type SConstructor      = Con () String
> type SPattern          = Pat () String String
> type SPatternTerm      = PatTerm () String String
> type SDeclaration      = Decl () String String
> type SDataDeclaration  = DataDecl () String String
> type SFunDeclaration   = FunDecl () String String
> type SProgram          = Prog () String String
> type SGuard            = Grd () String String