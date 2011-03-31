> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

> module Unify where

> import Control.Applicative
> import Control.Monad hiding (mapM_)
> import Data.Foldable 
> import Data.Maybe
> import Data.Monoid hiding (All)
> import Prelude hiding (any, mapM_)
> import Text.PrettyPrint.HughesPJ

> import BwdFwd
> import TyNum
> import Type
> import Syntax
> import Context
> import Num
> import Kit
> import Error
> import PrettyPrinter
> import PrettyContext

> data Extension = Restore | Replace Suffix

> onTop ::  (TyEntry -> Contextual t Extension)
>             -> Contextual t ()
> onTop f = do
>     c <- getContext
>     case c of
>         _Gamma :< A alphaD -> do
>             putContext _Gamma
>             ext (A alphaD) =<< f alphaD
>         _Gamma :< xD -> do
>             putContext _Gamma
>             onTop f
>             modifyContext (:< xD)
>         B0 -> erk $ "onTop: ran out of context"

> onTopNum ::  (NormalPredicate, Contextual t ()) ->
>                  (TyEntry -> Contextual t Extension) ->
>                  Contextual t ()
> onTopNum (p, m) f = do
>   g <- getContext
>   case g of
>     _Gamma :< xD -> do  
>       putContext _Gamma
>       case xD of
>         A (a := d ::: KindNum) -> ext xD =<< f (a := d ::: KindNum)
>         Layer pt@(PatternTop _ _ _ cs) -> do
>             m
>             modifyContext (:< Layer (pt{ptConstraints = p : cs}))
>         Layer GenMark -> do
>             m
>             modifyContext (:< Layer GenMark)
>             modifyContext (:< Constraint Wanted p)
> {-
>         Constraint Given _ -> do
>             m
>             modifyContext $ (:< xD) . (:< Constraint Wanted p)
> -}
>         _ -> onTopNum (p, m) f >> modifyContext (:< xD)
>     B0 -> inLocation (text "when solving" <+> prettyHigh p) $
>               erk $ "onTopNum: ran out of context"

> restore :: Contextual t Extension
> restore = return Restore

> replace :: Suffix -> Contextual t Extension
> replace = return . Replace

> ext :: Entry -> Extension -> Contextual t ()
> ext xD (Replace _Xi)  = modifyContext (<>< _Xi)
> ext xD Restore        = modifyContext (:< xD)

> class FV a where
>     (<?) :: TyName -> a -> Bool

> instance FV TyName where
>     (<?) = (==)

> instance FV a => FV (Ty k a) where
>     alpha <? t = any (alpha <?) t

> instance FV a => FV (TyDef a) where
>     alpha <? t = any (alpha <?) t

> instance FV a => FV (TyNum a) where
>     alpha <? t = any (alpha <?) t

> instance FV Suffix where
>     alpha <? t = any (alpha <?) t

> instance FV TyEntry where
>     alpha <? (a := d ::: k) = alpha <? a || alpha <? d

> instance FV NormalNum where
>     alpha <? n = isJust $ lookupVariable alpha n

> instance FV NormalPredicate where
>     alpha <? IsPos n   = alpha <? n
>     alpha <? IsZero n  = alpha <? n

> instance FV a => FV [a] where
>     alpha <? as = any (alpha <?) as

> instance (FV a, Ord a, Trav3 t) => FV (t k a x) where
>     alpha <? t = getAny $ getKonst $ trav3 (Const . Any . (alpha <?))
>                                            (Const . Any . (alpha <?))
>                                            (const $ Const $ Any False) t
>       where
>         getKonst :: Const a (t l () y) -> a
>         getKonst = getConst

> instance (FV a, FV b) => FV (Either a b) where
>     alpha <? Left x = alpha <? x
>     alpha <? Right y = alpha <? y

> (<??) :: TyName -> Entry -> Bool
> a <?? (A e) = a <? e
> a <?? (Constraint _ p) = a <? p
> a <?? (Func _ ty) = a <? ty
> a <?? (Layer l) = a <? l

> unify t u = unifyTypes t u `inLoc` (do
>                 t' <- niceType t
>                 u' <- niceType u
>                 g <- getContext
>                 return $ sep [text "when unifying", nest 4 (prettyHigh t),
>                              text "and", nest 4 (prettyHigh u)])
>                     -- ++ "\n    in context " ++ render g)

> unifyTypes :: Type -> Type -> Contextual t ()
> -- unifyTypes s t | s == t = return ()
> unifyTypes (TyB b) (TyB c) | b == c  = return ()
> unifyTypes (TyVar KindNum alpha) (TyVar KindNum beta) = unifyNum (NumVar alpha) (NumVar beta)
> unifyTypes (TyVar ka alpha) (TyVar kb beta) | ka /= kb   = erk "Kind mismatch in unify"
>                                             | otherwise  = onTop $
>   \ (gamma := d ::: k) -> case
>           (gamma == alpha, gamma == beta, d) of
>           (True,   True,   _)  ->  restore                                 

>           (True,   False,  Hole)      ->  replace ((alpha := Some (var k beta) ::: k) :> F0)
>           (True,   False,  Some tau)  ->  unifyTypes (TyVar kb beta)   tau       >> restore   
>           (True,   False,  _)          ->  solve beta ((alpha := d ::: k) :> F0) (TyVar ka alpha)
>                                       >>  replace F0

>           (False,  True,   Hole)      ->  replace ((beta := Some (var k alpha) ::: k) :> F0)
>           (False,  True,   Some tau)  ->  unifyTypes (TyVar ka alpha)  tau       >> restore   
>           (False,  True,   _)         ->  solve alpha ((beta := d ::: k) :> F0) (TyVar kb beta)
>                                       >>  replace F0

>           (False,  False,  _)         ->  unifyTypes (TyVar ka alpha)  (TyVar kb beta)  >> restore   

> unifyTypes (TyCon c1) (TyCon c2)
>     | c1 == c2   = return ()
>     | otherwise  = erk $ "Mismatched type constructors " ++ c1
>                               ++ " and " ++ c2

> unifyTypes (TyApp f1 s1) (TyApp f2 s2) = unifyTypes f1 f2 >> unifyTypes s1 s2



> {-
> unifyTypes (Bind b1 a1 k1 t1) (Bind b2 a2 k2 t2) | b1 == b2 && k1 == k2 = do
>     nm <- fresh (a1 ++ "_u") (Fixed ::: KindNum)
>     unifyTypes (unbind nm t1) (unbind nm t2)
> -}

> {-
> unifyTypes (Bind b a k ty) tau = do
>     nm <- fresh a (Hole ::: k)
>     unifyTypes (unbind nm ty) tau

> unifyTypes tau (Bind b a k ty) = do
>     nm <- fresh a (Hole ::: k)
>     unifyTypes tau (unbind nm ty)
> -}


> -- unifyTypes (Qual p s) (Qual q t) | p == q = unifyTypes s t

> {-
> unifyTypes (Qual p t) tau = do
>     p <- normalisePred p
>     modifyContext (:< Constraint Wanted p)
>     unifyTypes t tau
> unifyTypes tau (Qual p t) = do
>     p <- normalisePred p
>     modifyContext (:< Constraint Wanted p)
>     unifyTypes tau t
> -}

> {-
> unifyTypes (Qual p s) (Qual q t) = do
>     unifyTypes s t
>     g <- getContext
>     let p' = expandPred g p
>         q' = expandPred g q
>     unless (p' == q') $ erk $ "Mismatched qualifiers " ++ renderMe p' ++ " and " ++ renderMe q'
> -}

> unifyTypes (TyNum m)      (TyNum n)              = unifyNum m n
> unifyTypes (TyNum m)      (TyVar KindNum a)      = unifyNum m (NumVar a)
> unifyTypes (TyVar KindNum a)      (TyNum n)      = unifyNum (NumVar a) n

> unifyTypes (TyVar k alpha)  tau              =  startSolve alpha tau
> unifyTypes tau              (TyVar k alpha)  =  startSolve alpha tau
> unifyTypes tau              upsilon = errCannotUnify tau upsilon



> startSolve :: TyName -> Type -> Contextual t ()
> startSolve alpha tau = do
>     (rho, xs) <- rigidHull tau
>     solve alpha (pairsToSuffix xs) rho
>     unifyPairs xs

> rigidHull :: Type -> Contextual t (Type, Fwd (TyName, TypeNum))
> rigidHull (TyVar KindNum a)      = do  beta <- freshS "_j"
>                                        return (TyNum (NumVar beta), (beta, NumVar a) :> F0)
> rigidHull (TyVar k a)            = return (TyVar k a, F0)
> rigidHull (TyCon c)              = return (TyCon c, F0)
> rigidHull (TyApp f s)            = do  (f',  xs  )  <- rigidHull f
>                                        (s',  ys  )  <- rigidHull s
>                                        return (TyApp f' s', xs <.> ys)
> rigidHull (TyB b) = return (TyB b, F0)
> rigidHull (TyNum d)          = do  beta <- freshS "_i"
>                                    return (TyNum (NumVar beta), (beta, d) :> F0)
> rigidHull (Bind All x k b) | k /= KindNum = do
>     n <- freshName
>     (t, cs) <- rigidHull (unbind ("magic", n) b)
>     return (Bind All x k (bind ("magic", n) t), cs)

> {-
> rigidHull (Bind Pi x KindNum b) = do
>     n <- freshName
>     (t, cs) <- rigidHull (unbind ("magic", n) b)
>     return (Bind Pi x KindNum (bind ("magic", n) t), dropMagic ("magic", n) cs)
>   where
>     dropMagic :: Eq a => a -> Fwd (a, b) -> Fwd (a, b)
>     dropMagic a F0 = F0
>     dropMagic a ((x, y) :> xys) | x == a     = dropMagic a xys
>                                 | otherwise  = (x, y) :> dropMagic a xys
> -}

> rigidHull (Qual p t) = (\ (t, cs) -> (Qual p t, cs)) <$> rigidHull t


> rigidHull b = erk $ "rigidHull can't cope with " ++ renderMe b

> pairsToSuffix :: Fwd (TyName, TypeNum) -> Suffix
> pairsToSuffix = fmap ((:= Hole ::: KindNum) . fst)

> unifyPairs :: Fwd (TyName, TypeNum) -> Contextual t ()
> unifyPairs = mapM_ (uncurry $ unifyNum . NumVar)


> solve :: TyName -> Suffix -> Type -> Contextual t ()
> solve alpha _Xi tau = onTop $
>   \ (gamma := d ::: k) -> let occurs = gamma <? tau || gamma <? _Xi in case
>     (gamma == alpha, occurs, d) of

>     (True,   True,   _)             ->  erk "Occurrence detected!"

>     (True,   False,  Hole)          ->  replace (_Xi <.> ((alpha := Some tau ::: k) :> F0))
>     (True,   False,  Some upsilon)  ->  modifyContext (<>< _Xi)
>                                         >>  unifyTypes upsilon tau
>                                         >>  restore
>     (True,   False,  _)             ->  errUnifyFixed alpha tau

>     (False,  True,   Some upsilon)  ->  do
>         (upsilon', xs) <- rigidHull upsilon
>         solve alpha (pairsToSuffix xs <.> ((gamma := Some upsilon' ::: k) :> _Xi)) tau
>         unifyPairs xs
>         replace F0
>     (False,  True,   _)             ->  solve alpha ((gamma := d ::: k) :> _Xi) tau
>                                         >>  replace F0   
>     (False,  False,  _)             ->  solve alpha _Xi tau
>                                         >>  restore



> unifyNum :: TypeNum -> TypeNum -> Contextual t ()
> unifyNum (NumConst 0) n = unifyZero F0 =<< normaliseNum n
> unifyNum m n = unifyZero F0 =<< normaliseNum (m - n)


> typeToNum :: Type -> Contextual t NormalNum
> typeToNum (TyNum n)          = normaliseNum n
> typeToNum (TyVar KindNum a)  = lookupNormNumVar a
> typeToNum t = erk $ "Bad type in numeric constraint: " ++ show t

> lookupNormNumVar :: TyName -> Contextual t NormalNum
> lookupNormNumVar a = getContext >>= seek
>   where
>     seek B0 = erk $ "Missing numeric variable " ++ show a
>     seek (g :< A (b := _ ::: k))
>         | a == b && k == KindNum = return $ mkVar a
>         | a == b = erk $ "Type variable " ++ show a ++ " is not numeric"
>     seek (g :< _) = seek g

> constrainZero :: NormalNum -> Contextual t ()
> constrainZero e = modifyContext (:< Constraint Wanted (IsZero e))

> unifyZero :: Suffix -> NormalNum -> Contextual t ()
> unifyZero _Psi e
>   | isZero e      = return ()
>   | isConstant e  = errCannotUnify (numToType e) (TyNum (NumConst 0))
>   | otherwise     = onTopNum (IsZero e, modifyContext (<>< _Psi)) $
>     \ (alpha := d ::: KindNum) ->
>     case lookupVariable alpha e of
>       Nothing -> unifyZero _Psi e >> restore
>       Just n -> case d of
>         Some x -> do
>             modifyContext (<>< _Psi)
>             x' <- typeToNum x
>             unifyZero F0 (substNum alpha x' e)
>             restore
>         Hole  | n `dividesCoeffs` e -> do
>                   modifyContext (<>< _Psi)
>                   replace $ (alpha := Some (numToType (pivot (alpha, n) e)) ::: KindNum) :> F0
>               | (alpha, n) `notMaxCoeff` e -> do
>                   modifyContext (<>< _Psi)
>                   error "this really ought to be tested"
>                   (p, beta) <- insertFreshVar $ pivot (alpha, n) e
>                   unifyZero ((beta := Hole ::: KindNum) :> F0) $ substNExp (alpha, n) p e
>                   replace $ (alpha := Some (numToType p) ::: KindNum) :> F0
>         _  | numVariables e > fwdLength _Psi + 1 -> do
>                          unifyZero ((alpha := d ::: KindNum) :> _Psi) e
>                          replace F0
>            | otherwise -> do
>                modifyContext (:< A (alpha := d ::: KindNum))
>                modifyContext (<>< _Psi)
>                constrainZero e
>                replace F0
>                --g <- getContext
>                --erk $ "No way for " ++ render e ++ " in " ++
>                --           render g ++ "; " ++ render (alpha := d ::: KindNum) ++ " | " ++ render _Psi


> subsPreds a dn = map (substNormPred a dn)

> findRewrite :: TyName -> [NormalPredicate] -> Maybe NormalNum
> findRewrite a hs = listToMaybe $ catMaybes $ map (toRewrite a) hs

> toRewrite :: TyName -> NormalPredicate -> Maybe NormalNum
> toRewrite a (IsZero n) = case lookupVariable a n of
>     Just i | i `dividesCoeffs` n  -> Just $ pivot (a, i) n
>     _                             -> Nothing
> toRewrite a (IsPos _) = Nothing



We can insert a fresh variable into a unit thus:

> insertFreshVar :: NormalNum -> Contextual t (NormalNum, TyName)
> insertFreshVar d = do
>     beta <- freshS "_beta"
>     return (d +~ mkVar beta, beta)



> unifyFun :: Rho -> Contextual a (Sigma, Rho)
> unifyFun (TyApp (TyApp (TyB Arr) s) t) = return (s, t)
> unifyFun ty = do
>     n <- freshName
>     a <- unknownTyVar $ "_dom" ++ show n ::: Set
>     b <- unknownTyVar $ "_cod" ++ show n ::: Set
>     unify (a --> b) ty
>     return (a, b)
