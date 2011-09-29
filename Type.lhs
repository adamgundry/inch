> {-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable,
>              GADTs, TypeOperators, TypeFamilies, RankNTypes,
>              ScopedTypeVariables, FlexibleInstances,
>              StandaloneDeriving, TypeSynonymInstances #-}

> module Type where

> import Control.Applicative
> import Data.Foldable hiding (notElem)
> import Data.Maybe
> import Data.Traversable

> import Kit
> import Kind
> import Num


> type NVar a     = Var a KNum
> type NormNum a  = NExp a

> type Predicate        = Pred TypeNum
> type NormalNum        = NormNum (NVar ())
> type NormalPredicate  = NormPred NormalNum

> type SPredicate       = Pred SType
> type SNormalNum       = NormNum String
> type SNormalPred      = NormPred SNormalNum

> type TyNum a  = Ty a KNum
> type TypeNum  = TyNum ()

> type Type k  = Ty () k
> type Tau     = Type KSet
> type Sigma   = Type KSet
> type Rho     = Type KSet



> data Comparator = LE | LS | GE | GR | EL
>   deriving (Eq, Show)

> data Pred ty where
>     P  :: Comparator -> ty -> ty -> Pred ty
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> (%==%), (%<=%), (%<%), (%>=%), (%>%) :: forall ty. ty -> ty -> Pred ty
> (%==%)  = P EL
> (%<=%)  = P LE
> (%<%)   = P LS
> (%>=%)  = P GE
> (%>%)   = P GR

> data NormPred ty where
>     IsPos   :: ty -> NormPred ty
>     IsZero  :: ty -> NormPred ty
>   deriving (Eq, Show, Functor, Foldable, Traversable)



> bindNormPred ::  (Eq a, Eq b) => (a -> NormNum b) ->
>                      NormPred (NormNum a) -> NormPred (NormNum b)
> bindNormPred g = fmap (bindNExp g)

> substNormPred ::  Eq a => a -> NormNum a ->
>                       NormPred (NormNum a) -> NormPred (NormNum a)
> substNormPred a n = fmap (substNum a n)




> data BinOp = Plus | Minus | Times
>   deriving (Eq, Show)

> {-
>     Pow    :: NumOp (KNum :-> KNum :-> KNum)
>     Min    :: NumOp (KNum :-> KNum :-> KNum)
>     Max    :: NumOp (KNum :-> KNum :-> KNum)
>     Abs    :: NumOp (KNum :-> KNum)
>     Sig    :: NumOp (KNum :-> KNum)
>     Mod    :: NumOp (KNum :-> KNum :-> KNum)
> -}

> binOpString :: BinOp -> String
> binOpString Plus   = "+"
> binOpString Minus  = "-"
> binOpString Times  = "*"



> data TyKind where
>     TK :: Type k -> Kind k -> TyKind


> data Ty a k where
>     TyVar  :: Var a k                                       -> Ty a k
>     TyCon  :: TyConName -> Kind k                           -> Ty a k
>     TyApp  :: Ty a (l :-> k) -> Ty a l                      -> Ty a k
>     Bind   :: Binder -> String -> Kind l -> Ty (a, l) KSet  -> Ty a KSet
>     Qual   :: Pred (Ty a KNum) -> Ty a KSet                 -> Ty a KSet
>     Arr    :: Ty a (KSet :-> KSet :-> KSet)
>     TyInt  :: Integer                                       -> Ty a KNum
>     BinOp  :: BinOp                                         -> Ty a (KNum :-> KNum :-> KNum)

> deriving instance Show (Ty a k)

> instance FV (Ty a k) where
>     a <? t = elemTy (wkClosedVar a) t

> instance Eq (Ty a k) where

> instance Num (Ty a KNum) where
>     fromInteger  = TyInt
>     (+)          = TyApp . TyApp (BinOp Plus)
>     (*)          = TyApp . TyApp (BinOp Times)
>     (-)          = TyApp . TyApp (BinOp Minus)

> data SType where
>     STyVar  :: String                              ->  SType
>     STyCon  :: TyConName                           ->  SType
>     STyApp  :: SType -> SType                      ->  SType
>     SBind   :: Binder -> String -> SKind -> SType  ->  SType
>     SQual   :: Pred SType -> SType                 ->  SType
>     SArr    ::                                         SType
>     STyInt  :: Integer                             ->  SType
>     SBinOp  :: BinOp                               ->  SType
>   deriving (Eq, Show)

> instance Num SType where
>     fromInteger  = STyInt
>     (+)          = STyApp . STyApp (SBinOp Plus)
>     (*)          = STyApp . STyApp (SBinOp Times)
>     (-)          = STyApp . STyApp (SBinOp Minus)



> fogTy :: Type k -> SType
> fogTy = fogTy' fogVar []

> fogSysTy :: Type k -> SType
> fogSysTy = fogTy' fogSysVar []

> fogTy' :: (forall l. Var a l -> String) -> [String] -> Ty a k -> SType
> fogTy' g _   (TyVar v)       = STyVar (g v)
> fogTy' _ _   (TyCon c k)     = STyCon c
> fogTy' g xs  (TyApp f s)     = STyApp (fogTy' g xs f) (fogTy' g xs s)
> fogTy' g xs  (Qual p t)      = SQual (fmap (fogTy' g xs) p) (fogTy' g xs t)
> fogTy' _ _   Arr             = SArr
> fogTy' _ _   (TyInt i)       = STyInt i
> fogTy' _ _   (BinOp o)       = SBinOp o
> fogTy' g xs  (Bind b x k t)  =
>     SBind b y (fogKind k) (fogTy' (wkn g) (y:xs) t)
>   where
>     y = alphaConv x xs

>     wkn :: (forall l'. Var a l' -> String) -> Var (a, k) l -> String
>     wkn g (BVar Top)      = y
>     wkn g (BVar (Pop x))  = g (BVar x)
>     wkn g (FVar a k)      = g (FVar a k)

> fogPred :: Predicate -> SPredicate
> fogPred = fogPred' fogVar []

> fogSysPred :: Predicate -> SPredicate
> fogSysPred = fogPred' fogSysVar []

> fogPred' :: (forall l. Var a l -> String) -> [String] -> Pred (Ty a KNum) -> SPredicate
> fogPred' g xs = fmap (fogTy' g xs)


> fogNormNum :: NormalNum -> SNormalNum
> fogNormNum = fogNormNum' fogVar

> fogSysNormNum :: NormalNum -> SNormalNum
> fogSysNormNum = fogNormNum' fogSysVar

> fogNormNum' :: (NVar a -> String) -> NormNum (NVar a) -> SNormalNum
> fogNormNum' = fmap


> fogNormPred :: NormalPredicate -> SNormalPred
> fogNormPred = fogNormPred' fogVar

> fogSysNormPred :: NormalPredicate -> SNormalPred
> fogSysNormPred = fogNormPred' fogSysVar

> fogNormPred' :: (NVar a -> String) -> NormPred (NormNum (NVar a)) -> SNormalPred
> fogNormPred' = fmap . fogNormNum'



> alphaConv :: String -> [String] -> String
> alphaConv x xs | x `notElem` xs = x
>                | otherwise = alphaConv (x ++ "'") xs

> getTyKind :: Type k -> Kind k
> getTyKind (TyVar v)        = varKind v
> getTyKind (TyCon c k)      = k
> getTyKind (TyApp f s)      = case getTyKind f of _ :-> k -> k
> getTyKind (TyInt _)        = KNum
> getTyKind (BinOp _)        = KNum :-> KNum :-> KNum
> getTyKind (Qual _ _)       = KSet
> getTyKind (Bind _ _ __ _)  = KSet
> getTyKind Arr              = KSet :-> KSet :-> KSet

> (-->) :: forall a. Ty a KSet -> Ty a KSet -> Ty a KSet
> s --> t = TyApp (TyApp Arr s) t
> infixr 5 -->

> (--->) :: SType -> SType -> SType
> s ---> t = STyApp (STyApp SArr s) t
> infixr 5 --->


> (/->) :: Foldable f => f (Ty a KSet) -> Ty a KSet -> Ty a KSet
> ts /-> t = Data.Foldable.foldr (-->) t ts

> (/=>) :: Foldable f => f (Pred (Ty a KNum)) -> Ty a KSet -> Ty a KSet
> ps /=> t = Data.Foldable.foldr Qual t ps


> swapTop :: Ty ((a, k), l) x -> Ty ((a, l), k) x
> swapTop = renameTy (withBVar swapVar)
>   where
>     swapVar :: BVar ((a, k), l) x -> BVar ((a, l), k) x
>     swapVar Top            = Pop Top
>     swapVar (Pop Top)      = Top
>     swapVar (Pop (Pop x))  = Pop (Pop x)

> renameTy :: (forall k. Var a k -> Var b k) -> Ty a l -> Ty b l
> renameTy g (TyVar v)       = TyVar (g v)
> renameTy g (TyCon c k)     = TyCon c k
> renameTy g (TyApp f s)     = TyApp (renameTy g f) (renameTy g s)
> renameTy g (Bind b x k t)  = Bind b x k (renameTy (wkRenaming g) t)
> renameTy g (Qual p t)      = Qual (fmap (renameTy g) p) (renameTy g t)
> renameTy g Arr             = Arr
> renameTy g (TyInt i)       = TyInt i
> renameTy g (BinOp o)       = BinOp o

> bindTy :: Var a k -> Ty a l -> Ty (a, k) l
> bindTy v = renameTy (bindVar v)

> unbindTy :: Var a k -> Ty (a, k) l -> Ty a l
> unbindTy v = renameTy (unbindVar v)

> wkTy :: Ty a k -> Ty (a, l) k
> wkTy = renameTy wkVar

> wkClosedTy :: Ty () k -> Ty a k
> wkClosedTy = renameTy wkClosedVar

> wkSubst :: (Var a k -> Ty b k) -> Var (a, l) k -> Ty (b, l) k
> wkSubst g (FVar a k)      = wkTy (g (FVar a k))
> wkSubst g (BVar Top)      = TyVar (BVar Top)
> wkSubst g (BVar (Pop x))  = wkTy (g (BVar x))

> substTy :: (forall k . Var a k -> Ty b k) -> Ty a l -> Ty b l
> substTy g (TyVar v)       = g v
> substTy g (TyCon c k)     = TyCon c k
> substTy g (TyApp f s)     = TyApp (substTy g f) (substTy g s)
> substTy g (Bind b x k t)  = Bind b x k (substTy (wkSubst g) t)
> substTy g (Qual p t)      = Qual (fmap (substTy g) p) (substTy g t)
> substTy g Arr             = Arr
> substTy g (TyInt i)       = TyInt i
> substTy g (BinOp o)       = BinOp o

> replaceTy :: forall a k l. Var a k -> Ty a k -> Ty a l -> Ty a l
> replaceTy a u = substTy f
>   where
>     f :: Var a k' -> Ty a k'
>     f b@(FVar (N _ _ (UserVar Pi)) KNum) = TyVar b -- This is a hack to avoid replacing pivars
>     f b = hetEq a b u (TyVar b)



> simplifyTy :: Ord a => Ty a KSet -> Ty a KSet
> simplifyTy = simplifyTy' []
>   where
>     simplifyTy' :: Ord a => [Pred (Ty a KNum)] -> Ty a KSet -> Ty a KSet
>     simplifyTy' ps (Qual p t)      = simplifyTy' (simplifyPred p:ps) t
>     simplifyTy' ps t               = {-nub-} ps /=> t

> simplifyPred :: Pred (Ty a KNum) -> Pred (Ty a KNum)
> simplifyPred (P c m n) = case (simplifyNum m, simplifyNum n) of
>     (TyApp (TyApp (BinOp Minus) m') n', TyInt 0)  -> mkP c m' n'
>     (TyInt 0, TyApp (TyApp (BinOp Minus) n') m')  -> mkP c m' n'
>     (m', n')                                      -> mkP c m' n'
>   where
>     mkP LE m (TyApp (TyApp (BinOp Minus) m') (TyInt 1)) = P LS m n
>     mkP c m n = P c m n

> simplifyNum :: Ty a KNum -> Ty a KNum
> simplifyNum (TyApp (TyApp (BinOp o) n) m) = case (o, simplifyNum n, simplifyNum m) of
>     (Plus,   TyInt k,  TyInt l)  -> TyInt (k+l)
>     (Plus,   TyInt 0,  m')       -> m'
>     (Plus,   n',       TyInt 0)  -> n'
>     (Plus,   TyApp (TyApp (BinOp Plus) n') (TyInt k), TyInt l)  | k == -l    -> n'
>                                                         | otherwise  -> n' + TyInt (k+l)
>     (Plus,   n',       m')       -> n' + m'
>     (Times,  TyInt k,     TyInt l)     -> TyInt (k*l)
>     (Times,  TyInt 0,     m')          -> TyInt 0
>     (Times,  TyInt 1,     m')          -> m'
>     (Times,  TyInt (-1),  m')          -> negate m'
>     (Times,  n',          TyInt 0)     -> TyInt 0
>     (Times,  n',          TyInt 1)     -> n'
>     (Times,  n',          TyInt (-1))  -> negate n'
>     (Times,  n',          m')          -> n' * m'
>     (Minus,  n',          m')          -> n' - m'
> simplifyNum t = t


> args :: Ty a k -> Int
> args (TyApp (TyApp Arr _) t)  = succ $ args t
> args (Bind Pi  _ _ t)                = succ $ args t
> args (Bind All _ _ t)               = args t
> args (Qual _ t)                     = args t
> args _                              = 0

> splitArgs :: Ty a k -> ([Ty a k], Ty a k)
> splitArgs (TyApp (TyApp Arr s) t) = (s:ss, ty)
>   where (ss, ty) = splitArgs t
> splitArgs t = ([], t)

> targets :: Ty a k -> TyConName -> Bool
> targets (TyCon c _)               t | c == t = True
> targets (TyApp (TyApp Arr _) ty)  t = targets ty t
> targets (TyApp f _)               t = targets f t
> targets (Bind _ _ _ ty)           t = targets ty t
> targets (Qual _ ty)               t = targets ty t
> targets _                         _ = False

> numToType :: NormalNum -> Type KNum
> numToType  = reifyNum


> elemTy :: Var a k -> Ty a l -> Bool
> elemTy a (TyVar b)       = a =?= b
> elemTy a (TyApp f s)     = elemTy a f || elemTy a s
> elemTy a (Bind b x k t)  = elemTy (wkVar a) t
> elemTy a (Qual (P _ m n) t) = elemTy a m || elemTy a n || elemTy a t 
> elemTy a _               = False

> elemTarget :: Var a k -> Ty a l -> Bool
> elemTarget a (TyApp (TyApp Arr _) ty)  = elemTarget a ty
> elemTarget a (Qual _ ty)               = elemTarget a ty
> elemTarget a (Bind Pi x k ty)          = elemTarget (wkVar a) ty
> elemTarget a t                         = elemTy a t

> elemPred :: Var a k -> Pred (Ty a KNum) -> Bool
> elemPred a (P c m n) = elemTy a m || elemTy a n



> reifyNum :: NormNum (NVar a) -> Ty a KNum
> reifyNum = simplifyNum . foldNExp (\ k n m -> TyInt k * TyVar n + m) TyInt

> reifyPred :: NormPred (NormNum (NVar a)) -> Pred (Ty a KNum)
> reifyPred (IsPos n) = simplifyPred $ TyInt 0 %<=% reifyNum n
> reifyPred (IsZero n) = simplifyPred $ reifyNum n %==% TyInt 0



> normaliseNum :: Ord a => Ty a KNum -> Maybe (NormNum (NVar a))
> normaliseNum (TyInt i)     = return $ mkConstant i
> normaliseNum (TyVar a)     = return $ mkVar a
> normaliseNum (TyApp (TyApp (BinOp o) m) n) = do
>     m <- normaliseNum m
>     n <- normaliseNum n
>     case o of
>         Plus   -> return $ m +~ n
>         Minus  -> return $ m -~ n
>         Times  -> case (getConstant m, getConstant n) of
>             (Just i, Just j) -> return $ mkConstant (i * j)
>             (Just i,   Nothing)  -> return $ i *~ n
>             (Nothing,  Just j)   -> return $ j *~ m
>             (Nothing,  Nothing)  -> Nothing
> normaliseNum t = Nothing

> normalNum s t = maybe (error $ "normalNum: cannot normalise " ++ show t) id $ normaliseNum t

> normalisePred ::  Ord a => Pred (Ty a KNum) -> Maybe (NormPred (NormNum (NVar a)))
> normalisePred (P LE m n)  = IsPos <$> normaliseNum (n - m)
> normalisePred (P LS m n)  = IsPos <$> normaliseNum (n - (m + 1))
> normalisePred (P GE m n)  = IsPos <$> normaliseNum (m - n)
> normalisePred (P GR m n)  = IsPos <$> normaliseNum (m - (n + 1))
> normalisePred (P EL m n)  = IsZero <$> normaliseNum (n - m)


> trivialPred :: Ord a => Pred (Ty a KNum) -> Maybe Bool
> trivialPred p = trivialNormPred =<< normalisePred p

> trivialNormPred (IsPos n)   = (>= 0) <$> getConstant n
> trivialNormPred (IsZero n)  = (== 0) <$> getConstant n


> instance FV NormalNum where
>     a@(FVar _ KNum) <? n = isJust $ lookupVariable a n
>     _ <? _               = False

> instance FV NormalPredicate where
>     a <? IsPos n   = a <? n
>     a <? IsZero n  = a <? n