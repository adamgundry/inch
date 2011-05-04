> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
>              GADTs, TypeOperators, FlexibleInstances,
>              StandaloneDeriving, TypeFamilies, RankNTypes #-}

> module Syntax where

> import Control.Applicative
> import Control.Monad
> import Data.Foldable hiding (foldl1)
> import Data.Traversable
> import Data.Monoid

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
> type Program          = Prog OK
> type Guard            = Grd OK

> type STerm             = Tm RAW
> type SConstructor      = Con RAW
> type SPattern          = Pat RAW
> type SPatternTerm      = PatTerm RAW
> type SDeclaration      = Decl RAW
> type SProgram          = Prog RAW
> type SGuard            = Grd RAW



> class TravTypes t where
>     travTypes :: Applicative f =>
>         (forall k. Type k -> f (Type k)) -> t OK -> f (t OK)
>     fogTypes :: (forall k. Var () k -> String) -> t OK -> t RAW

> mapTypes :: TravTypes t =>
>                 (forall k. Type k -> Type k) -> t OK -> t OK
> mapTypes g = unId . travTypes (Id . g)

> replaceTypes :: TravTypes t => Var () k -> Type k -> t OK -> t OK
> replaceTypes a t = mapTypes (replaceTy a t)

> elemTypes :: TravTypes t => Var () k -> t OK -> Bool
> elemTypes a t = getAny $ getConst $ travTypes (Const . Any . (a <?)) t


> fog :: TravTypes t => t OK -> t RAW
> fog = fogTypes fogVar

> fogSys :: TravTypes t => t OK -> t RAW
> fogSys = fogTypes fogSysVar


> data Tm s where
>     TmVar    :: TmName                -> Tm s
>     TmCon    :: TmConName             -> Tm s
>     TmInt    :: Integer               -> Tm s
>     TmApp    :: Tm s -> Tm s          -> Tm s
>     TmBrace  :: TyNum (AVar KNum s)   -> Tm s
>     Lam      :: TmName -> Tm s        -> Tm s
>     Let      :: [Decl s] -> Tm s      -> Tm s
>     (:?)     :: Tm s -> AType KSet s  -> Tm s

> deriving instance Eq (Tm RAW)

> instance TravTypes Tm where
>     travTypes g (TmApp f s)  = TmApp <$> travTypes g f <*> travTypes g s
>     travTypes g (TmBrace n)  = TmBrace . toNum <$> g (TyNum n)
>     travTypes g (Lam x b)    = Lam x <$> travTypes g b
>     travTypes g (Let ds t)   = Let <$> traverse (travTypes g) ds
>                                    <*> travTypes g t
>     travTypes g (t :? ty)    = (:?) <$> travTypes g t <*> g ty
>     travTypes g t            = pure t
>
>     fogTypes g (TmVar x)     = TmVar x
>     fogTypes g (TmCon c)     = TmCon c
>     fogTypes g (TmInt k)     = TmInt k
>     fogTypes g (TmApp f s)   = TmApp (fogTypes g f) (fogTypes g s)
>     fogTypes g (TmBrace n)   = TmBrace (fogTyNum' g n)
>     fogTypes g (Lam x b)     = Lam x (fogTypes g b)
>     fogTypes g (Let ds t)    = Let (map (fogTypes g) ds)
>                                    (fogTypes g t)
>     fogTypes g (t :? ty)     = fogTypes g t :? fogTy' g [] ty



> data Decl s where
>     DataDecl  :: TyConName -> AKind k s -> [TmConName ::: AType KSet s] ->
>                      Decl s
>     FunDecl   :: TmName -> [Pat s] -> Decl s
>     SigDecl   :: TmName -> AType KSet s -> Decl s

> deriving instance Eq (Decl RAW)

> instance TravTypes Decl where
>     travTypes g (DataDecl x k cs) =
>         DataDecl x k <$> traverse (\ (x ::: t) -> (x :::) <$> g t) cs
>     travTypes g (FunDecl x ps) =
>         FunDecl x <$> traverse (travTypes g) ps
>     travTypes g (SigDecl x ty) = SigDecl x <$> g ty
>
>     fogTypes g (DataDecl x k cs) = DataDecl x (fogKind k)
>         (map (\ (x ::: t) -> x ::: fogTy' g [] t) cs)
>     fogTypes g (FunDecl x ps)  = FunDecl x (map (fogTypes g) ps)
>     fogTypes g (SigDecl x ty)  = SigDecl x (fogTy' g [] ty)






> data Pat s where
>     Pat :: [PatTerm s] -> Maybe (Grd s) -> Tm s -> Pat s

> deriving instance Eq (Pat RAW)

> instance TravTypes Pat where
>     travTypes g (Pat xs ms t) = 
>         Pat <$> traverse (travTypes g) xs
>             <*> traverse (travTypes g) ms
>             <*> travTypes g t
>
>     fogTypes g (Pat xs ms t) = 
>         Pat (map (fogTypes g) xs)
>             (fmap (fogTypes g) ms)
>             (fogTypes g t)

> instance FV (Pat OK) where
>     (<?) = elemTypes

> isVarPat :: Pat s -> Bool
> isVarPat (Pat [] Nothing _)  = True
> isVarPat _                   = False


> data PatTerm s where
>     PatVar     :: TmName -> PatTerm s
>     PatCon     :: TmConName -> [PatTerm s] -> PatTerm s
>     PatIgnore  :: PatTerm s
>     PatBrace   :: Maybe TmName -> Integer -> PatTerm s

> deriving instance Eq (PatTerm RAW)

> instance TravTypes PatTerm where
>     travTypes g t = pure t -- change if types added to pattern terms
>     fogTypes g (PatVar x)       = PatVar x
>     fogTypes g (PatCon x ps)    = PatCon x (map (fogTypes g) ps)
>     fogTypes g PatIgnore        = PatIgnore
>     fogTypes g (PatBrace mt k)  = PatBrace mt k



> data Grd s where
>     ExpGuard  :: Tm s -> Grd s
>     NumGuard  :: [Pred (AVar KNum s)] -> Grd s

> deriving instance Eq (Grd RAW)

> instance TravTypes Grd where
>     travTypes g (ExpGuard t)   = ExpGuard <$> travTypes g t
>     travTypes g (NumGuard ps)  = NumGuard <$> traverse (travPred gn) ps
>       where gn = (toNum <$>) . g . TyNum
>
>     fogTypes g (ExpGuard t)  = ExpGuard (fogTypes g t)
>     fogTypes g (NumGuard ps) = NumGuard (map (fogPred' g) ps)
