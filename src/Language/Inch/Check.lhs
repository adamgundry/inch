> {-# LANGUAGE FlexibleContexts #-}

> module Language.Inch.Check where

> import Prelude hiding (all)
> import Control.Applicative
> import Control.Monad
> import Data.Monoid
> import Data.Foldable
> import Control.Monad.State

> import Language.Inch.BwdFwd
> import Language.Inch.Context
> import Language.Inch.Error
> import Language.Inch.Kit
> import Language.Inch.Kind hiding (All)
> import Language.Inch.Type
> import Language.Inch.PrettyPrinter
> import Language.Inch.Syntax


Set this to True in order to verify the context regularly:

> paranoid :: Bool
> paranoid = False

> traceContext :: MonadState ZipState m => String -> m ()
> traceContext s = getContext >>= \ g -> mtrace (s ++ "\n" ++ renderMe g)

> defines :: Context -> Var () k -> Bool
> defines B0                 _            = False
> defines (_ :< A (b := _))  a | a =?= b  = True
> defines (g :< _)           a            = defines g a

> goodCx :: Context -> Bool
> goodCx B0 = True
> goodCx (g :< e) = goodEntry g e && goodCx g

> goodEntry :: Context -> Entry -> Bool
> goodEntry g (A (a := d))      = not (g `defines` a) && goodTyDef g d
> goodEntry g (Constraint _ p)  = goodTy g p
> goodEntry g (Layer l _)       = goodLayer g l

> goodTyDef :: Context -> TyDef k -> Bool
> goodTyDef g (Some t)  = goodTy g t
> goodTyDef _ Hole      = True
> goodTyDef _ Fixed     = True
> goodTyDef _ Exists    = True

> goodFV :: FV t () => Context -> t -> Bool
> goodFV g = getAll . fvFoldMap (All . defines g)

> goodLayer :: Context -> TmLayer -> Bool
> goodLayer g (PatternTop (_ ::: s))  = goodTy g s
> goodLayer _ CaseTop                 = True
> goodLayer _ FunTop                  = True
> goodLayer _ GenMark                 = True
> goodLayer _ GuardTop                = True
> goodLayer g (LamBody (_ ::: t))     = goodTy g t
> goodLayer g (LetBindings bs)        = goodBindings g bs
> goodLayer g (LetBody bs)            = goodBindings g bs

> goodBindings :: Context -> Bindings -> Bool
> goodBindings g = all (maybe True (goodTy g) . fst)


> goodTy :: Context -> Type k -> Bool
> goodTy = goodFV

> goodDecl :: Context -> Declaration () -> Bool
> goodDecl g (SigDecl _ t)        = goodTy g t
> goodDecl _ (FunDecl _ _)        = True


> verifyContext :: Bool -> String -> Contextual ()
> verifyContext before s | paranoid = do
>     g <- getContext
>     unless (goodCx g) $ do
>         traceContext $ "verifyContext: failed " ++ (if before then "before " else "after ") ++ s
>         erk "Game over."
>     return ()
> verifyContext _ _ = return ()

> wrapVerify :: String -> Contextual t -> Contextual t
> wrapVerify s m = verifyContext True s *> m <* verifyContext False s



> assertContextEmpty :: Contextual ()
> assertContextEmpty = do
>     g <- getContext
>     case g of
>         B0  -> return ()
>         _   -> traceContext "assertContextEmpty" >> erk "Error: context is not empty"