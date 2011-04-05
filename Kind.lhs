> {-# LANGUAGE GADTs, TypeOperators, TypeFamilies, RankNTypes, FlexibleInstances #-}

> module Kind where

> import Kit

> type TyName           = (String, Int)
> type TmName           = String
> type TyConName        = String
> type TmConName        = String


> data KSet
> data KNum
> data k :-> l

> data Kind k where
>     KSet   :: Kind KSet
>     KNum   :: Kind KNum
>     (:->)  :: Kind k -> Kind l -> Kind (k :-> l)

> data SKind where
>     SKSet   :: SKind
>     SKNum   :: SKind
>     (:-->)  :: SKind -> SKind -> SKind
>   deriving (Eq, Show)

> infixr 5 :->

> targetsSet :: Kind k -> Bool
> targetsSet KSet       = True
> targetsSet KNum       = False
> targetsSet (_ :-> k)  = targetsSet k 

> fogKind :: Kind k -> SKind
> fogKind KSet       = SKSet
> fogKind KNum       = SKNum
> fogKind (k :-> l)  = fogKind k :--> fogKind l

> varName :: Var () k -> TyName
> varName (FVar a _) = a

> varKind :: Var () k -> Kind k
> varKind (FVar _ k) = k

> kindKind :: SKind -> Ex Kind
> kindKind SKSet = Ex KSet
> kindKind SKNum = Ex KNum
> kindKind (k :--> l) = case (kindKind k, kindKind l) of
>                            (Ex k, Ex l) -> Ex (k :-> l)
>                 


> instance HetEq Kind where
>     hetEq KSet KSet yes no = yes
>     hetEq KNum KNum yes no = yes
>     hetEq (k :-> k') (l :-> l') yes no = hetEq k l (hetEq k' l' yes no) no
>     hetEq _ _ yes no = no


> data Binder where
>     Pi   :: Binder
>     All  :: Binder
>   deriving (Eq, Show)

> data Var a k where
>     BVar :: BVar a k          -> Var a k
>     FVar :: TyName -> Kind k  -> Var a k

> instance Show (Var a k) where
>     show (BVar x)    = show x
>     show (FVar a _)  = show a

> instance Eq (Var a k) where
>     BVar x    == BVar y    = x == y
>     FVar a _  == FVar b _  = a == b
>     _         == _         = False

> instance Ord (Var a k) where
>     BVar x    <= BVar y    = x <= y
>     FVar a _  <= FVar b _  = a <= b
>     BVar _    <= FVar _ _  = True
>     FVar _ _  <= BVar _    = False

> data BVar a k where
>     Top  :: BVar (a, k) k
>     Pop  :: BVar a k -> BVar (a, l) k

> bvarToInt :: BVar a k -> Int
> bvarToInt Top      = 0
> bvarToInt (Pop x)  = succ (bvarToInt x)

> fogVar :: [String] -> Var a k -> String
> fogVar bs (FVar a k) = fst a
> fogVar bs (BVar x) = bs !! bvarToInt x

> instance Show (BVar a k) where
>     show x = '!' : show (bvarToInt x)

> instance Eq (BVar a k) where
>     Top    == Top    = True
>     Pop x  == Pop y  = x == y
>     _      == _      = False

> instance Ord (BVar a k) where
>     Top    <= _      = True
>     Pop x  <= Pop y  = x <= y
>     Pop _  <= Top    = False



> instance HetEq (BVar a) where
>     hetEq Top      Top      yes no = yes
>     hetEq (Pop x)  (Pop y)  yes no = hetEq x y yes no
>     hetEq _        _        yes no = no

> instance HetEq (Var a) where
>     hetEq (FVar a k)  (FVar b l)  yes no | a == b = hetEq k l yes
>                                                        (error "eqVar: kinding error")
>     hetEq (BVar x)    (BVar y)    yes no = hetEq x y yes no
>     hetEq _           _           yes no = no