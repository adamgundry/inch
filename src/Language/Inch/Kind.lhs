> {-# LANGUAGE GADTs, TypeOperators, TypeFamilies, RankNTypes,
>              FlexibleInstances, StandaloneDeriving, MultiParamTypeClasses,
>              FlexibleContexts, EmptyDataDecls #-}

> module Language.Inch.Kind where

> import Data.Foldable
> import Data.Map (Map)
> import qualified Data.Map as Map
> import Data.Monoid
> import Prelude hiding (any, elem)

> import Language.Inch.BwdFwd
> import Language.Inch.Kit



> type TmName           = String
> type TyConName        = String
> type TmConName        = String


> data Binder where
>     Pi   :: Binder
>     All  :: Binder
>   deriving (Eq, Ord, Show)

> data VarState where
>     UserVar  :: Binder -> VarState
>     SysVar   :: VarState
>   deriving (Eq, Ord, Show)

> data TyName where
>     N :: String -> Int -> VarState -> TyName
>   deriving (Eq, Ord, Show)

> nameToString :: TyName -> String
> nameToString (N s _ _) = s

> nameToSysString :: TyName -> String
> nameToSysString (N s i _) = s ++ "_" ++ show i

> nameEq :: TyName -> String -> Bool
> nameEq (N x _ (UserVar _)) y  = x == y
> nameEq (N _ _ SysVar)  _  = False

> nameBinder :: TyName -> Maybe Binder
> nameBinder (N _ _ (UserVar b))  = Just b
> nameBinder _                    = Nothing

> data KSet
> data KNum
> data KConstraint
> data k :-> l

> data Kind k where
>     KSet   :: Kind KSet
>     KNum   :: Kind KNum
>     KConstraint :: Kind KConstraint
>     (:->)  :: Kind k -> Kind l -> Kind (k :-> l)
> infixr 5 :->

> deriving instance Show (Kind k)

> instance HetEq Kind where
>     hetEq KSet KSet yes _ = yes
>     hetEq KNum KNum yes _ = yes
>     hetEq KConstraint KConstraint yes _ = yes
>     hetEq (k :-> k') (l :-> l') yes no = hetEq k l (hetEq k' l' yes no) no
>     hetEq _ _ _ no = no

> instance HetOrd Kind where
>     KSet  <?=  _               = True
>     _     <?=  KSet            = False
>     KNum  <?=  _               = True
>     _     <?=  KNum            = False
>     KConstraint <?= _            = True
>     _           <?= KConstraint  = False
>     (k :-> k') <?= (l :-> l')  = k <?= k' && l <?= l'

> class KindI t where
>     kind :: Kind t

> instance KindI KSet where
>     kind = KSet

> instance KindI KNum where
>     kind = KNum

> instance (KindI k, KindI l) => KindI (k :-> l) where
>     kind = kind :-> kind

> data SKind where
>     SKSet   :: SKind
>     SKNum   :: SKind
>     SKNat   :: SKind
>     SKConstraint :: SKind
>     (:-->)  :: SKind -> SKind -> SKind
>   deriving (Eq, Show)
> infixr 5 :-->


> targetsSet :: Kind k -> Bool
> targetsSet KSet       = True
> targetsSet KNum       = False
> targetsSet KConstraint = False
> targetsSet (_ :-> k)  = targetsSet k 

> fogKind :: Kind k -> SKind
> fogKind KSet       = SKSet
> fogKind KNum       = SKNum
> fogKind KConstraint = SKConstraint
> fogKind (k :-> l)  = fogKind k :--> fogKind l

> kindKind :: SKind -> Ex Kind
> kindKind SKSet       = Ex KSet
> kindKind SKNum       = Ex KNum
> kindKind SKNat       = Ex KNum
> kindKind SKConstraint = Ex KConstraint
> kindKind (k :--> l)  = case (kindKind k, kindKind l) of
>                            (Ex k', Ex l') -> Ex (k' :-> l')

> kindCod :: Kind (k :-> l) -> Kind l
> kindCod (_ :-> l) = l







> data BVar a k where
>     Top  :: BVar (a, k) k
>     Pop  :: BVar a k -> BVar (a, l) k

> instance Show (BVar a k) where
>     show x = '!' : show (bvarToInt x)

> instance HetEq (BVar a) where
>     hetEq Top      Top      yes _  = yes
>     hetEq (Pop x)  (Pop y)  yes no = hetEq x y yes no
>     hetEq _        _        _   no = no

> instance Eq (BVar a k) where
>     (==) = (=?=)

> instance HetOrd (BVar a) where
>     Top    <?= _      = True
>     Pop x  <?= Pop y  = x <?= y
>     Pop _  <?= Top    = False

> instance Ord (BVar a k) where
>     (<=) = (<?=)



> bvarToInt :: BVar a k -> Int
> bvarToInt Top      = 0
> bvarToInt (Pop x)  = succ (bvarToInt x)



> data Var a k where
>     BVar :: BVar a k          -> Var a k
>     FVar :: TyName -> Kind k  -> Var a k

> instance Show (Var a k) where
>     show (BVar x)    = show x
>     show (FVar a _)  = show a

> instance HetEq (Var a) where
>     hetEq (FVar a k)  (FVar b l)  yes _ | a == b =
>         hetEq k l yes (error "eqVar: kinding error")
>     hetEq (BVar x)    (BVar y)    yes no = hetEq x y yes no
>     hetEq _           _           _   no = no

> instance Eq (Var a k) where
>     (==) = (=?=)

> instance HetOrd (Var a) where
>     BVar x    <?= BVar y    = x <?= y
>     FVar a _  <?= FVar b _  = a <= b
>     BVar _    <?= FVar _ _  = True
>     FVar _ _  <?= BVar _    = False

> instance Ord (Var a k) where
>     (<=) = (<?=)


> impossibleBVar :: BVar () k -> a
> impossibleBVar b = error $ "impossible BVar: " ++ show b

> varName :: Var () k -> TyName
> varName (FVar a _)  = a
> varName (BVar b)    = impossibleBVar b

> varKind :: Var () k -> Kind k
> varKind (FVar _ k)  = k
> varKind (BVar b)    = impossibleBVar b

> varBinder :: Var () k -> Maybe Binder
> varBinder (FVar a _)  = nameBinder a
> varBinder (BVar b)    = impossibleBVar b

> fogVar :: Var () k -> String
> fogVar = fogVar' nameToString []

> fogSysVar :: Var () k -> String
> fogSysVar = fogVar' nameToSysString []

> fogVar' :: (TyName -> String) -> [String] -> Var a k -> String
> fogVar' g _  (FVar a _)  = g a
> fogVar' _ bs (BVar x)    = bs !! bvarToInt x

> varNameEq :: Var a k -> String -> Bool
> varNameEq (FVar nom _)  y = nameEq nom y
> varNameEq (BVar _)      _ = False

> wkF :: (forall k . Var a k -> t) -> t -> Var (a, l) k' -> t
> wkF f _ (FVar a k)      = f (FVar a k)
> wkF _ t (BVar Top)      = t
> wkF f _ (BVar (Pop y))  = f (BVar y)


> withBVar :: (BVar a k -> BVar b k) -> Var a k -> Var b k
> withBVar _ (FVar a k)  = FVar a k
> withBVar f (BVar x)    = BVar (f x)

> wkVar :: Var a k -> Var (a, l) k
> wkVar = withBVar Pop

> wkRenaming :: (Var a k -> Var b k) -> Var (a, l) k -> Var (b, l) k
> wkRenaming g (FVar a k)      = wkVar . g $ FVar a k
> wkRenaming _ (BVar Top)      = BVar Top
> wkRenaming g (BVar (Pop x))  = wkVar . g $ BVar x

> bindVar :: Var a k -> Var a l -> Var (a, k) l
> bindVar v w = hetEq v w (BVar Top) (wkVar w)

> unbindVar :: Var a k -> Var (a, k) l -> Var a l 
> unbindVar v (BVar Top)      = v
> unbindVar _ (BVar (Pop x))  = BVar x
> unbindVar _ (FVar a k)      = FVar a k

> wkClosedVar :: Var () k -> Var a k
> wkClosedVar (FVar a k)  = FVar a k
> wkClosedVar (BVar b)    = impossibleBVar b

> fixKind :: Kind k -> Var () l -> Maybe (Var () k)
> fixKind k v = hetEq k (varKind v) (Just v) Nothing

> fixNum :: Var () l -> Maybe (Var () KNum)
> fixNum = fixKind KNum  


> class FV t a where
>     fvFoldMap :: Monoid m => (forall k . Var a k -> m) -> t -> m

> (<<?) :: FV t a => [Ex (Var a)] -> t -> Bool
> as <<? t = getAny $ fvFoldMap (Any . (`hetElem` as)) t

> (<?) :: FV t a => Var a k -> t -> Bool
> a <? t = [Ex a] <<? t

> vars :: FV t a => t -> [Ex (Var a)]
> vars = fvFoldMap (\ x -> [Ex x])

> numvars :: FV t () => t -> [Var () KNum]
> numvars = fvFoldMap f
>   where
>     f :: Var () k -> [Var () KNum]
>     f a@(FVar _ KNum)  = [a]
>     f _                = []


> instance FV (Var a l) a where
>     fvFoldMap f a = f a

> instance FV t a => FV [t] a where
>     fvFoldMap f = foldMap (fvFoldMap f)

> instance FV t a => FV (Fwd t) a where
>     fvFoldMap f = foldMap (fvFoldMap f)

> instance FV t a => FV (Bwd t) a where
>     fvFoldMap f = foldMap (fvFoldMap f)

> instance (FV t a, FV u a) => FV (Either t u) a where
>     fvFoldMap f (Left x)   = fvFoldMap f x
>     fvFoldMap f (Right x)  = fvFoldMap f x

> instance (FV t a, FV u a) => FV (t, u) a where
>     fvFoldMap f (x, y) = fvFoldMap f x <.> fvFoldMap f y

> instance (FV s a, FV t a, FV u a) => FV (s, t, u) a where
>     fvFoldMap f (x, y, z) = fvFoldMap f x <.> fvFoldMap f y <.> fvFoldMap f z

> instance (Ord t, FV t a) => FV (Map t x) a where
>     fvFoldMap f = Map.foldrWithKey (\ t _ m -> fvFoldMap f t <.> m) mempty


> data VarSuffix a b where
>     VS0    :: VarSuffix a a
>     (:<<)  :: VarSuffix a b -> Var a k -> VarSuffix a (b, k)

> renameBVarVS :: VarSuffix a b -> BVar a k -> BVar b k
> renameBVarVS VS0         x = x
> renameBVarVS (vs :<< _)  x = Pop (renameBVarVS vs x)

> renameVS :: VarSuffix a b -> Var a k -> Var b k
> renameVS _   (FVar a k)  = FVar a k
> renameVS vs  (BVar x)    = BVar (renameBVarVS vs x)

> renameVSinv :: VarSuffix a b -> Var b k -> Var a k
> renameVSinv _          (FVar a k)      = FVar a k
> renameVSinv VS0        (BVar v)        = BVar v
> renameVSinv (_ :<< v)  (BVar Top)      = v
> renameVSinv (vs :<< _) (BVar (Pop x))  = renameVSinv vs (BVar x)