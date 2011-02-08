> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

> module Unify where

> import Data.Foldable 
> import Prelude hiding (any)

> import BwdFwd
> import Syntax
> import Context


> data Extension = Restore | Replace Suffix

> onTop ::  (TyEntry -> Contextual t Extension)
>             -> Contextual t ()
> onTop f = do
>     _Gamma :< vD <- getContext
>     putContext _Gamma
>     case vD of
>         A alphaD  -> do  m <- f alphaD
>                          case m of
>                              Replace _Xi  -> modifyContext (<>< _Xi)
>                              Restore      -> modifyContext (:< vD)
>         _         -> onTop f >> modifyContext (:< vD)

> restore :: Contextual t Extension
> restore = return Restore

> replace :: Suffix -> Contextual t Extension
> replace = return . Replace


> class FV a where
>     (<?) :: TyName -> a -> Bool

> instance FV TyName where
>     (<?) = (==)

> instance FV a => FV (Ty a) where
>     alpha <? t = any (alpha <?) t

> instance FV a => FV (Maybe a) where
>     alpha <? t = any (alpha <?) t

> instance FV Suffix where
>     alpha <? t = any (alpha <?) t

> instance FV TyEntry where
>     alpha <? (a := d ::: k) = alpha <? a || alpha <? d

> unify :: Ty TyName -> Ty TyName -> Contextual t ()
> unify Arr Arr = return ()
> unify (TyVar alpha)        (TyVar beta)                 = onTop $
>   \ (gamma := d ::: k) -> case
>           (gamma == alpha,  gamma == beta,  d         ) of
>           (True,            True,           _         )  ->  restore                                 
>           (True,            False,          Nothing   )  ->  replace ((alpha := Just (TyVar beta) ::: k) :> F0)
>           (False,           True,           Nothing   )  ->  replace ((beta := Just (TyVar alpha) ::: k) :> F0)
>           (True,            False,          Just tau  )  ->  unify (TyVar beta)   tau       >> restore   
>           (False,           True,           Just tau  )  ->  unify (TyVar alpha)  tau       >> restore   
>           (False,           False,          _         )  ->  unify (TyVar alpha)  (TyVar beta)  >> restore   

> unify (TyCon c1) (TyCon c2)
>     | c1 == c2   = return ()
>     | otherwise  = fail $ "Mismatched type constructors " ++ fst c1
>                               ++ " and " ++ fst c2

> unify (TyApp f1 s1) (TyApp f2 s2) = unify f1 f2 >> unify s1 s2

> unify (Bind b a k ty) tau = do
>     nm <- fresh a (Nothing ::: k)
>     unify (unbind nm ty) tau

> unify (TyVar alpha)  tau            =  solve alpha F0 tau
> unify tau            (TyVar alpha)  =  solve alpha F0 tau
> unify tau            upsilon        =  fail $ "Could not unify " ++ show tau ++ " and " ++ show upsilon

> solve :: TyName -> Suffix -> Ty TyName -> Contextual t ()
> solve alpha _Xi tau = onTop $
>   \ (gamma := d ::: k) -> let occurs = gamma <? tau || gamma <? _Xi in case
>     (gamma == alpha,  occurs,  d             ) of
>     (True,            True,    _             )  ->  fail "Occurrence detected!"
>     (True,            False,   Nothing       )  ->  replace (_Xi <+> ((alpha := Just tau ::: k) :> F0))
>     (True,            False,   Just upsilon  )  ->  modifyContext (<>< _Xi)
>                                                 >>  unify upsilon tau
>                                                 >>  restore
>     (False,           True,    _             )  ->  solve alpha ((gamma := d ::: k) :> _Xi) tau
>                                                 >>  replace F0   
>     (False,           False,   _             )  ->  solve alpha _Xi tau
>                                                 >>  restore
