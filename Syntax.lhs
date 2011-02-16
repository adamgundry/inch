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


> data Tm a x where
>     TmVar  :: x -> Tm a x
>     TmCon  :: TmConName -> Tm a x
>     TmApp  :: Tm a x -> Tm a x -> Tm a x
>     Lam    :: String -> Tm a (S x) -> Tm a x
>     (:?)   :: Tm a x -> Ty a -> Tm a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> instance Monad (Tm a) where
>     return = TmVar
>     TmVar x    >>= g = g x
>     TmCon c    >>= g = TmCon c
>     TmApp f s  >>= g = TmApp (f >>= g) (s >>= g)
>     Lam x t    >>= g = Lam x (t >>= wk g)
>     (t :? ty)  >>= g = (t >>= g) :? ty


> data DataDecl a x where
>     DataDecl  :: TyConName -> Kind -> [TmConName ::: Ty a] -> DataDecl a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)


> data FunDecl a x where
>     FunDecl   :: x -> Maybe (Ty a) -> [Pat a x] -> FunDecl a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data Decl a x where
>     DD :: DataDecl a x  -> Decl a x
>     FD :: FunDecl a x   -> Decl a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data Pat a x where
>     Pat :: [PatTerm a x] -> Guard a x -> Tm a x -> Pat a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data PatTerm a x where
>     PatVar  :: x -> PatTerm a x
>     PatCon  :: TmConName -> [PatTerm a x] -> PatTerm a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data Guard a x where
>     Trivial :: Guard a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)




> traverseTypes :: Applicative f => (Ty a -> f (Ty b)) -> Tm a x -> f (Tm b x)
> traverseTypes g (TmVar x) = pure $ TmVar x
> traverseTypes g (TmCon c) = pure $ TmCon c
> traverseTypes g (TmApp f s) = TmApp <$> traverseTypes g f <*> traverseTypes g s
> traverseTypes g (Lam x t) = Lam x <$> traverseTypes g t
> traverseTypes g (t :? ty) = (:?) <$> traverseTypes g t <*> g ty

> mapTypes :: (Ty a -> Ty b) -> Tm a x -> Tm b x
> mapTypes f t = unId $ traverseTypes (Id . f) t

> bindTypes :: (a -> Ty b) -> Tm a x -> Tm b x
> bindTypes f = mapTypes (f =<<)




> instance Bitraversable Tm where
>     bitraverse f g (TmVar x)    = TmVar <$> g x
>     bitraverse f g (TmCon c)    = pure (TmCon c)
>     bitraverse f g (TmApp t s)  = TmApp <$> bitraverse f g t <*> bitraverse f g s
>     bitraverse f g (Lam x t)    = Lam x <$> bitraverse f (traverse g) t
>     bitraverse f g (t :? ty)    = (:?) <$> bitraverse f g t <*> traverse f ty

> instance Bifunctor Tm where
>     bimap = bimapDefault

> instance Bifoldable Tm where
>     bifoldMap = bifoldMapDefault

> instance Bitraversable DataDecl where
>     bitraverse f g (DataDecl x k cs) =
>         DataDecl x k <$> traverse (traverse (traverse f)) cs

> instance Bifunctor DataDecl where
>     bimap = bimapDefault

> instance Bifoldable DataDecl where
>     bifoldMap = bifoldMapDefault

> instance Bitraversable FunDecl where
>     bitraverse f g (FunDecl x mt ps) =
>         FunDecl <$> g x <*> traverse (traverse f) mt <*> traverse (bitraverse f g) ps

> instance Bifunctor FunDecl where
>     bimap = bimapDefault

> instance Bifoldable FunDecl where
>     bifoldMap = bifoldMapDefault

> instance Bitraversable Decl where
>     bitraverse f g (DD d) = DD <$> bitraverse f g d
>     bitraverse f g (FD d) = FD <$> bitraverse f g d

> instance Bifunctor Decl where
>     bimap = bimapDefault

> instance Bifoldable Decl where
>     bifoldMap = bifoldMapDefault

> instance Bitraversable Pat where
>     bitraverse f g (Pat pts r t) =
>         Pat <$> traverse (bitraverse f g) pts <*> bitraverse f g r <*> bitraverse f g t

> instance Bifunctor Pat where
>     bimap = bimapDefault

> instance Bifoldable Pat where
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


> type Prog a x         = [Decl a x]
> type Con a            = TmConName ::: Ty a

> type Term             = Tm TyName TmName
> type Constructor      = Con TyName
> type Pattern          = Pat TyName TmName
> type PatternTerm      = PatTerm TyName TmName
> type Declaration      = Decl TyName TmName
> type DataDeclaration  = DataDecl TyName TmName
> type FunDeclaration   = FunDecl TyName TmName
> type Program          = Prog TyName TmName


> patToTm :: PatTerm a x -> Tm a x
> patToTm (PatVar a)     = TmVar a
> patToTm (PatCon a ps)  = foldl1 TmApp (TmCon a : map patToTm ps)