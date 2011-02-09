> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GADTs #-}

> module Syntax where

> import Data.Foldable hiding (foldl1)
> import Data.Traversable

> data S a where
>     S :: a -> S a
>     Z :: S a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> bind :: (Functor f, Eq a) => a -> f a -> f (S a)
> bind x = fmap inS
>   where  inS y | x == y     = Z
>                | otherwise  = S y

> unbind :: Functor f => a -> f (S a) -> f a
> unbind x = fmap unS
>   where  unS Z      = x
>          unS (S a)  = a

> data Kind where
>     Set      :: Kind
>     KindNat  :: Kind
>     KindArr  :: Kind -> Kind -> Kind
>   deriving (Eq, Show)

> k1 ---> k2 = KindArr k1 k2
> infixr 5 --->

> data Binder where
>     Pi   :: Binder
>     All  :: Binder
>   deriving (Eq, Show)

> data Ty a where
>     TyVar  :: a -> Ty a
>     TyCon  :: a -> Ty a
>     TyApp  :: Ty a -> Ty a -> Ty a
>     Arr    :: Ty a
>     Bind   :: Binder -> String -> Kind -> Ty (S a) -> Ty a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> s --> t = TyApp (TyApp Arr s) t
> infixr 5 -->

> subst :: Eq a => a -> Ty a -> Ty a -> Ty a
> subst a t (TyVar b) | a == b = t
>                     | otherwise = TyVar b
> subst a t (TyCon c) = TyCon c
> subst a t (TyApp f s) = TyApp (subst a t f) (subst a t s)
> subst a t Arr = Arr
> subst a t (Bind b s k u) = Bind b s k (subst (S a) (fmap S t) u)

> alphaConvert :: [(String, String)] -> Ty a -> Ty a
> alphaConvert xys (TyApp f s) = TyApp (alphaConvert xys f)
>                                      (alphaConvert xys s)
> alphaConvert xys (Bind b a k t) = case lookup a xys of
>     Just y   -> Bind b y k (alphaConvert ((a, y ++ "'") : xys) t)
>     Nothing  -> Bind b a k (alphaConvert xys t)
> alphaConvert xys t = t

> data Tm a where
>     TmVar  :: a -> Tm a
>     TmCon  :: a -> Tm a
>     TmApp  :: Tm a -> Tm a -> Tm a
>     Lam    :: String -> Tm (S a) -> Tm a 
>     (:?)   :: Tm a -> Ty a -> Tm a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> substTm :: Eq a => a -> Tm a -> Tm a -> Tm a
> substTm x t (TmVar y)  | x == y     = t
>                      | otherwise  = TmVar y
> substTm x t (TmCon c) = TmCon c
> substTm x t (TmApp f s) = TmApp (substTm x t f) (substTm x t s)
> substTm x t (Lam s u) = Lam s (substTm (S x) (fmap S t) u)

> class Bifunctor f where
>     bimap :: (a -> c) -> (b -> d) -> f a b -> f c d

> data DataDecl tyv tmv where
>     DataDecl  :: tyv -> Kind -> [Con tyv tmv] -> DataDecl tyv tmv
>   deriving (Eq, Show)

> instance Bifunctor DataDecl where
>     bimap f g (DataDecl t k cs) = DataDecl (f t) k (map (bimap f g) cs)

> data FunDecl tyv tmv where
>     FunDecl   :: tmv -> Maybe (Ty tyv) -> [Pat tmv] -> FunDecl tyv tmv
>   deriving (Eq, Show)

> instance Bifunctor FunDecl where
>     bimap f g (FunDecl t mt ps) = FunDecl (g t) (fmap (fmap f) mt) (map (fmap g) ps)

> data Decl tyv tmv where
>     DD :: DataDecl tyv tmv  -> Decl tyv tmv
>     FD :: FunDecl tyv tmv   -> Decl tyv tmv
>   deriving (Eq, Show)

> instance Bifunctor Decl where
>     bimap f g (DD d) = DD (bimap f g d)
>     bimap f g (FD d) = FD (bimap f g d)

> data Con tyv tmv where
>     Con :: tmv -> Ty tyv -> Con tyv tmv
>   deriving (Eq, Show)

> instance Bifunctor Con where
>     bimap f g (Con t ty) = Con (g t) (fmap f ty)

> data Pat tmv where
>     Pat :: [PatTerm tmv] -> Guard tmv -> Tm tmv -> Pat tmv
>   deriving (Eq, Show, Functor)

> data PatTerm tmv where
>     PatVar  :: tmv -> PatTerm tmv
>     PatCon  :: tmv -> [PatTerm tmv] -> PatTerm tmv
>   deriving (Eq, Show, Functor)

> data Guard tmv where
>     Trivial :: Guard tmv
>   deriving (Eq, Show, Functor)


> type TyName           = (String, Int)
> type TmName           = String
> type Term             = Tm TmName
> type Type             = Ty TyName
> type Constructor      = Con TyName TmName
> type Pattern          = Pat TmName
> type PatternTerm      = PatTerm TmName
> type Declaration      = Decl TyName TmName
> type DataDeclaration  = DataDecl TyName TmName
> type FunDeclaration   = FunDecl TyName TmName
> type Prog tyv tmv     = [Decl tyv tmv]
> type Program          = [Declaration]


> patToTm :: PatTerm a -> Tm a
> patToTm (PatVar a)     = TmVar a
> patToTm (PatCon a ps)  = foldl1 TmApp (TmCon a : map patToTm ps)