> {-# LANGUAGE FlexibleContexts #-}

> module Check where

> import Prelude hiding (all)
> import Control.Applicative
> import Control.Monad
> import Data.Monoid
> import Data.Foldable

> import BwdFwd
> import Context
> import Error
> import Kit
> import Kind hiding (All)
> import Type
> import PrettyPrinter
> import PrettyContext ()
> import Syntax


> traceContext s = getContext >>= \ g -> mtrace (s ++ "\n" ++ renderMe g)

> defines :: Context -> Var () k -> Bool
> defines B0                 _            = False
> defines (g :< A (b := _))  a | a =?= b  = True
> defines (g :< _)           a            = defines g a

> goodCx :: Context -> Bool
> goodCx B0 = True
> goodCx (g :< e) = goodEntry g e && goodCx g

> goodEntry :: Context -> Entry -> Bool
> goodEntry g (A (a := d))      = not (g `defines` a) && goodTyDef g d
> goodEntry g (Constraint _ p)  = all (goodTy g) p
> goodEntry g (Layer l)         = goodLayer g l

> goodTyDef :: Context -> TyDef k -> Bool
> goodTyDef g (Some t)  = goodTy g t
> goodTyDef g Hole      = True
> goodTyDef g Fixed     = True
> goodTyDef g Exists    = True

> goodFV :: FV t () => Context -> t -> Bool
> goodFV g = getAll . fvFoldMap (All . defines g)

> goodLayer :: Context -> TmLayer -> Bool
> goodLayer g (PatternTop (_ ::: s))  = goodTy g s
> goodLayer g CaseTop                 = True
> goodLayer g FunTop                  = True
> goodLayer g GenMark                 = True
> goodLayer g GuardTop                = True
> goodLayer g (LamBody (_ ::: t))     = goodTy g t
> goodLayer g (LetBindings bs)        = goodBindings g bs
> goodLayer g (LetBody bs)            = goodBindings g bs

> goodBindings :: Context -> Bindings -> Bool
> goodBindings g = all (maybe True (goodTy g) . fst)


> goodTy :: Context -> Type k -> Bool
> goodTy = goodFV

> goodDecl :: Context -> Declaration () -> Bool
> goodDecl g (SigDecl _ t)      = goodTy g t
> goodDecl g (DataDecl _ _ cs)  = all (\ (_ ::: t) -> goodTy g t) cs
> goodDecl g (FunDecl _ _)      = True


> verifyContext :: Bool -> String -> Contextual ()
> verifyContext before s = do
>     g <- getContext
>     unless (goodCx g) $ do
>         traceContext $ "verifyContext: failed " ++ (if before then "before " else "after ") ++ s
>         erk "Game over."
>     return ()

> wrapVerify :: String -> Contextual t -> Contextual t
> wrapVerify s m = verifyContext True s *> m <* verifyContext False s