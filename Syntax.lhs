> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, GADTs, TypeOperators #-}

> module Syntax where

> import Control.Applicative
> import Data.Foldable hiding (foldl1)
> import Data.Traversable
> import Data.Bifunctor
> import Data.Bifoldable
> import Data.Bitraversable

> import Kit

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

> simplifyNum :: TyNum a -> TyNum a
> simplifyNum (n :+: m) = case (simplifyNum n, simplifyNum m) of
>     (NumConst k,  NumConst l)  -> NumConst (k+l)
>     (NumConst 0,  m')          -> m'
>     (n',          NumConst 0)  -> n'
>     (n',          m')          -> n' :+: m'
> simplifyNum (n :*: m) = case (simplifyNum n, simplifyNum m) of
>     (NumConst k,     NumConst l)     -> NumConst (k*l)
>     (NumConst 0,     m')             -> NumConst 0
>     (NumConst 1,     m')             -> m'
>     (NumConst (-1),  m')             -> Neg m'
>     (n',             NumConst 0)     -> NumConst 0
>     (n',             NumConst 1)     -> n'
>     (n',             NumConst (-1))  -> Neg n'
>     (n',             m')             -> n' :*: m'
> simplifyNum (Neg n) = case simplifyNum n of
>     NumConst k  -> NumConst (-k)
>     n'          -> Neg n'
> simplifyNum t = t

> instance (Eq a, Show a) => Num (TyNum a) where
>     (+)          = (:+:)
>     (*)          = (:*:)
>     negate       = Neg
>     fromInteger  = NumConst
>     abs          = error "no abs"
>     signum       = error "no signum"


> substNum :: Eq a => a -> TyNum a -> TyNum a -> TyNum a
> substNum a m (NumVar b) | a == b = m
>                         | otherwise = NumVar b
> substNum a m (NumConst k) = NumConst k
> substNum a m (n1 :+: n2) = substNum a m n1 :+: substNum a m n2
> substNum a m (n1 :*: n2) = substNum a m n1 :*: substNum a m n2
> substNum a m (Neg n) = Neg (substNum a m n)

> data Ty a where
>     TyVar  :: a -> Ty a
>     TyCon  :: TyConName -> Ty a
>     TyApp  :: Ty a -> Ty a -> Ty a
>     Arr    :: Ty a
>     TyNum  :: TyNum a -> Ty a
>     Bind   :: Binder -> String -> Kind -> Ty (S a) -> Ty a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> s --> t = TyApp (TyApp Arr s) t
> infixr 5 -->

> simplifyTy :: Ty a -> Ty a
> simplifyTy (TyNum n)       = TyNum (simplifyNum n)
> simplifyTy (TyApp f s)     = TyApp (simplifyTy f) (simplifyTy s)
> simplifyTy (Bind b x k t)  = Bind b x k (simplifyTy t)
> simplifyTy t               = t

> subst :: Eq a => a -> Ty a -> Ty a -> Ty a
> subst a t (TyVar b) | a == b = t
>                     | otherwise = TyVar b
> subst a t (TyCon c) = TyCon c
> subst a t (TyApp f s) = TyApp (subst a t f) (subst a t s)
> subst a t Arr = Arr
> subst a (TyNum m) (TyNum n) = TyNum (substNum a m n)
> subst a t (TyNum n) = TyNum n
> subst a t (Bind b s k u) = Bind b s k (subst (S a) (fmap S t) u)

> alphaConvert :: [(String, String)] -> Ty a -> Ty a
> alphaConvert xys (TyApp f s) = TyApp (alphaConvert xys f)
>                                      (alphaConvert xys s)
> alphaConvert xys (Bind b a k t) = case lookup a xys of
>     Just y   -> Bind b y k (alphaConvert ((a, y ++ "'") : xys) t)
>     Nothing  -> Bind b a k (alphaConvert xys t)
> alphaConvert xys t = t

> args :: Ty a -> Int
> args (TyApp (TyApp Arr s) t) = succ $ args t
> args (Bind b x k t) = args t
> args _ = 0



> data Tm a x where
>     TmVar  :: x -> Tm a x
>     TmCon  :: TmConName -> Tm a x
>     TmApp  :: Tm a x -> Tm a x -> Tm a x
>     Lam    :: String -> Tm a (S x) -> Tm a x
>     (:?)   :: Tm a x -> Ty a -> Tm a x
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> substTm :: Eq x => x -> Tm a x -> Tm a x -> Tm a x
> substTm x t (TmVar y)  | x == y     = t
>                        | otherwise  = TmVar y
> substTm x t (TmCon c) = TmCon c
> substTm x t (TmApp f s) = TmApp (substTm x t f) (substTm x t s)
> substTm x t (Lam s u) = Lam s (substTm (S x) (fmap S t) u)


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

> type TyName           = (String, Int)
> type TmName           = String
> type TyConName        = String
> type TmConName        = String

> type Type             = Ty TyName
> type Term             = Tm TyName TmName
> type TypeNum          = TyNum TyName
> type Con a            = TmConName ::: Ty a
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