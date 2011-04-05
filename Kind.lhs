> {-# LANGUAGE GADTs, TypeOperators, TypeFamilies, RankNTypes,
>              FlexibleInstances #-}

> module Kind where

> import Data.Foldable
> import Prelude hiding (any)

> import BwdFwd
> import Kit



> type TmName           = String
> type TyConName        = String
> type TmConName        = String



> data VarState where
>     UserVar  :: VarState
>     SysVar   :: VarState
>   deriving (Eq, Ord, Show)

> data TyName where
>     N :: String -> Int -> VarState -> TyName
>   deriving (Eq, Ord, Show)

> nameToString :: TyName -> String
> nameToString (N s _ _) = s

> nameEq :: TyName -> String -> Bool
> nameEq (N x _ UserVar) y  = x == y
> nameEq (N _ _ SysVar)  _  = False


> data KSet
> data KNum
> data k :-> l

> data Kind k where
>     KSet   :: Kind KSet
>     KNum   :: Kind KNum
>     (:->)  :: Kind k -> Kind l -> Kind (k :-> l)
> infixr 5 :->

> instance HetEq Kind where
>     hetEq KSet KSet yes _ = yes
>     hetEq KNum KNum yes _ = yes
>     hetEq (k :-> k') (l :-> l') yes no = hetEq k l (hetEq k' l' yes no) no
>     hetEq _ _ _ no = no

> data SKind where
>     SKSet   :: SKind
>     SKNum   :: SKind
>     (:-->)  :: SKind -> SKind -> SKind
>   deriving (Eq, Show)
> infixr 5 :-->


> targetsSet :: Kind k -> Bool
> targetsSet KSet       = True
> targetsSet KNum       = False
> targetsSet (_ :-> k)  = targetsSet k 

> fogKind :: Kind k -> SKind
> fogKind KSet       = SKSet
> fogKind KNum       = SKNum
> fogKind (k :-> l)  = fogKind k :--> fogKind l

> kindKind :: SKind -> Ex Kind
> kindKind SKSet       = Ex KSet
> kindKind SKNum       = Ex KNum
> kindKind (k :--> l)  = case (kindKind k, kindKind l) of
>                            (Ex k, Ex l) -> Ex (k :-> l)








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

> instance Ord (BVar a k) where
>     Top    <= _      = True
>     Pop x  <= Pop y  = x <= y
>     Pop _  <= Top    = False


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

> instance Ord (Var a k) where
>     BVar x    <= BVar y    = x <= y
>     FVar a _  <= FVar b _  = a <= b
>     BVar _    <= FVar _ _  = True
>     FVar _ _  <= BVar _    = False


> varName :: Var () k -> TyName
> varName (FVar a _) = a

> varToString :: Var () k -> String
> varToString = nameToString . varName

> varKind :: Var () k -> Kind k
> varKind (FVar _ k) = k

> fogVar :: [String] -> Var a k -> String
> fogVar _  (FVar a _)  = nameToString a
> fogVar bs (BVar x)    = bs !! bvarToInt x

> varNameEq :: Var a k -> String -> Bool
> varNameEq (FVar nom _)  y = nameEq nom y
> varNameEq (BVar _)      _ = False




> class FV t where
>     (<?) :: Var () k -> t -> Bool

> instance FV (Var () l) where
>     (<?) = (=?=)

> instance FV a => FV [a] where
>     a <? as = any (a <?) as

> instance FV a => FV (Fwd a) where
>     a <? t = any (a <?) t

> instance FV a => FV (Bwd a) where
>     a <? t = any (a <?) t

> instance (FV a, FV b) => FV (Either a b) where
>     alpha <? Left x = alpha <? x
>     alpha <? Right y = alpha <? y
