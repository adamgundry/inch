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
>     KindNum  :: Kind
>     KindArr  :: Kind -> Kind -> Kind
>   deriving (Eq, Show)

> k1 ---> k2 = KindArr k1 k2
> infixr 5 --->

> data Binder where
>     Pi   :: Binder
>     All  :: Binder
>   deriving (Eq, Show)

> data TyNum a where
>     NumConst  :: Integer -> TyNum a
>     NumVar    :: a -> TyNum a
>     (:+:)     :: TyNum a -> TyNum a -> TyNum a
>     (:*:)     :: TyNum a -> TyNum a -> TyNum a
>     Neg       :: TyNum a -> TyNum a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> instance (Eq a, Show a) => Num (TyNum a) where
>     (+)          = (:+:)
>     (*)          = (:*:)
>     negate       = Neg
>     fromInteger  = NumConst
>     abs          = error "no abs"
>     signum       = error "no signum"

> data Ty a where
>     TyVar  :: a -> Ty a
>     TyCon  :: a -> Ty a
>     TyApp  :: Ty a -> Ty a -> Ty a
>     Arr    :: Ty a
>     TyNum  :: TyNum a -> Ty a
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
> subst a t (TyNum n) = TyNum n
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


> data DataDecl a where
>     DataDecl  :: a -> Kind -> [Con a] -> DataDecl a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data FunDecl a where
>     FunDecl   :: a -> Maybe (Ty a) -> [Pat a] -> FunDecl a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data Decl a where
>     DD :: DataDecl a  -> Decl a
>     FD :: FunDecl a   -> Decl a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data Con a where
>     Con :: a -> Ty a -> Con a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data Pat a where
>     Pat :: [PatTerm a] -> Guard a -> Tm a -> Pat a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data PatTerm a where
>     PatVar  :: a -> PatTerm a
>     PatCon  :: a -> [PatTerm a] -> PatTerm a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> data Guard a where
>     Trivial :: Guard a
>   deriving (Eq, Show, Functor, Foldable, Traversable)


> type Prog a           = [Decl a]

> type Name             = (String, Int)
> type Term             = Tm Name
> type Type             = Ty Name
> type TypeNum          = TyNum Name
> type Constructor      = Con Name
> type Pattern          = Pat Name
> type PatternTerm      = PatTerm Name
> type Declaration      = Decl Name
> type DataDeclaration  = DataDecl Name
> type FunDeclaration   = FunDecl Name
> type Program          = Prog Name


> patToTm :: PatTerm a -> Tm a
> patToTm (PatVar a)     = TmVar a
> patToTm (PatCon a ps)  = foldl1 TmApp (TmCon a : map patToTm ps)