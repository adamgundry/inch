> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GADTs, TypeOperators #-}

> module Syntax where

> import Control.Applicative
> import Data.Foldable hiding (foldl1)
> import Data.Traversable
> import Data.Bifunctor
> import Data.Bifoldable
> import Data.Bitraversable

> import Kit
> import Type


> data Tm k a x where
>     TmVar  :: x -> Tm k a x
>     TmCon  :: TmConName -> Tm k a x
>     TmApp  :: Tm k a x -> Tm k a x -> Tm k a x
>     Lam    :: String -> Tm k a (S x) -> Tm k a x
>     (:?)   :: Tm k a x -> Ty k a -> Tm k a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> instance Monad (Tm k a) where
>     return = TmVar
>     TmVar x    >>= g = g x
>     TmCon c    >>= g = TmCon c
>     TmApp f s  >>= g = TmApp (f >>= g) (s >>= g)
>     Lam x t    >>= g = Lam x (t >>= wk g)
>     (t :? ty)  >>= g = (t >>= g) :? ty


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
>     Pat :: [PatTerm a x] -> Guard a x -> Tm k a x -> Pat k a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data PatTerm a x where
>     PatVar  :: x -> PatTerm a x
>     PatCon  :: TmConName -> [PatTerm a x] -> PatTerm a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data Guard a x where
>     Trivial :: Guard a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)



> partitionDecls :: [Decl k a x] -> ([DataDecl k a x], [FunDecl k a x])
> partitionDecls [] = ([], [])
> partitionDecls (DD d : xs) = (d:ds, fs)
>   where (ds, fs) = partitionDecls xs
> partitionDecls (FD f : xs) = (ds, f:fs)
>   where (ds, fs) = partitionDecls xs


> traverseTypes :: Applicative f => (Ty k a -> f (Ty l b)) -> Tm k a x -> f (Tm l b x)
> traverseTypes g (TmVar x) = pure $ TmVar x
> traverseTypes g (TmCon c) = pure $ TmCon c
> traverseTypes g (TmApp f s) = TmApp <$> traverseTypes g f <*> traverseTypes g s
> traverseTypes g (Lam x t) = Lam x <$> traverseTypes g t
> traverseTypes g (t :? ty) = (:?) <$> traverseTypes g t <*> g ty

> mapTypes :: (Ty k a -> Ty l b) -> Tm k a x -> Tm l b x
> mapTypes f t = unId $ traverseTypes (Id . f) t

> bindTypes :: (Kind -> a -> Ty Kind b) -> Tm Kind a x -> Tm Kind b x
> bindTypes f = mapTypes (bindTy f)




> instance Bitraversable (Tm k) where
>     bitraverse f g (TmVar x)    = TmVar <$> g x
>     bitraverse f g (TmCon c)    = pure (TmCon c)
>     bitraverse f g (TmApp t s)  = TmApp <$> bitraverse f g t <*> bitraverse f g s
>     bitraverse f g (Lam x t)    = Lam x <$> bitraverse f (traverse g) t
>     bitraverse f g (t :? ty)    = (:?) <$> bitraverse f g t <*> traverse f ty

> instance Bifunctor (Tm k) where
>     bimap = bimapDefault

> instance Bifoldable (Tm k) where
>     bifoldMap = bifoldMapDefault

> instance Bitraversable (DataDecl k) where
>     bitraverse f g (DataDecl x k cs) =
>         DataDecl x k <$> traverse (traverse (traverse f)) cs

> instance Bifunctor (DataDecl k) where
>     bimap = bimapDefault

> instance Bifoldable (DataDecl k) where
>     bifoldMap = bifoldMapDefault

> instance Bitraversable (FunDecl k) where
>     bitraverse f g (FunDecl x mt ps) =
>         FunDecl <$> g x <*> traverse (traverse f) mt <*> traverse (bitraverse f g) ps

> instance Bifunctor (FunDecl k) where
>     bimap = bimapDefault

> instance Bifoldable (FunDecl k) where
>     bifoldMap = bifoldMapDefault

> instance Bitraversable (Decl k) where
>     bitraverse f g (DD d) = DD <$> bitraverse f g d
>     bitraverse f g (FD d) = FD <$> bitraverse f g d

> instance Bifunctor (Decl k) where
>     bimap = bimapDefault

> instance Bifoldable (Decl k) where
>     bifoldMap = bifoldMapDefault

> instance Bitraversable (Pat k) where
>     bitraverse f g (Pat pts r t) =
>         Pat <$> traverse (bitraverse f g) pts <*> bitraverse f g r <*> bitraverse f g t

> instance Bifunctor (Pat k) where
>     bimap = bimapDefault

> instance Bifoldable (Pat k) where
>     bifoldMap = bifoldMapDefault

> instance Bitraversable PatTerm where
>     bitraverse f g (PatVar x)      = PatVar <$> g x
>     bitraverse f g (PatCon c pts)  = PatCon c <$> traverse (bitraverse f g) pts

> instance Bifunctor PatTerm where
>     bimap = bimapDefault

> instance Bifoldable PatTerm where
>     bifoldMap = bifoldMapDefault

> instance Bitraversable Guard where
>     bitraverse f g Trivial = pure Trivial

> instance Bifunctor Guard where
>     bimap = bimapDefault

> instance Bifoldable Guard where
>     bifoldMap = bifoldMapDefault


> type Prog k a x       = [Decl k a x]
> type Con k a          = TmConName ::: Ty k a

> type Term             = Tm Kind TyName TmName
> type Constructor      = Con Kind TyName
> type Pattern          = Pat Kind TyName TmName
> type PatternTerm      = PatTerm TyName TmName
> type Declaration      = Decl Kind TyName TmName
> type DataDeclaration  = DataDecl Kind TyName TmName
> type FunDeclaration   = FunDecl Kind TyName TmName
> type Program          = Prog Kind TyName TmName

> type STerm             = Tm () String String
> type SConstructor      = Con () String
> type SPattern          = Pat () String String
> type SPatternTerm      = PatTerm String String
> type SDeclaration      = Decl () String String
> type SDataDeclaration  = DataDecl () String String
> type SFunDeclaration   = FunDecl () String String
> type SProgram          = Prog () String String

> patToTm :: PatTerm a x -> Tm k a x
> patToTm (PatVar a)     = TmVar a
> patToTm (PatCon a ps)  = foldl1 TmApp (TmCon a : map patToTm ps)