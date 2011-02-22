> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts #-}

> module ProgramCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Bitraversable

> import BwdFwd
> import TyNum
> import Type
> import Num
> import Syntax
> import Context
> import Unify
> import Orphans
> import Kit
> import Error
> import PrettyPrinter
> import KindCheck
> import TypeCheck


> typeCheck p = runStateT (checkProg p) initialState

> checkProg :: Prog String String -> Contextual () Program
> checkProg = mapM checkDecl 

> checkDecl :: Decl String String -> Contextual () Declaration
> checkDecl (DD d) = DD <$> checkDataDecl d
> checkDecl (FD f) = FD <$> checkFunDecl f
>     

> checkDataDecl :: DataDecl String String -> Contextual () DataDeclaration
> checkDataDecl (DataDecl t k cs) = inLocation ("in data type " ++ t) $ do
>     unless (targetsSet k) $ errKindTarget k
>     insertTyCon t k
>     DataDecl t k <$> mapM (checkConstructor t) cs

> checkConstructor :: TyConName -> Con String -> Contextual () Constructor
> checkConstructor t (c ::: ty) = inLocation ("in constructor " ++ c) $ do
>     (ty' ::: k) <- inferKind B0 ty
>     unless (k == Set) $ errKindNotSet k
>     unless (ty' `targets` t) $ errConstructorTarget ty'
>     insertTmCon c ty'
>     return (c ::: ty')

> checkFunDecl :: FunDecl String String -> Contextual () FunDeclaration
> checkFunDecl (FunDecl s Nothing pats@(Pat xs _ _ : _)) =
>   inLocation ("in declaration of " ++ s) $ do
>     modifyContext (:< Layer FunTop)
>     sty     <- TyVar <$> fresh "sty" (Hole ::: Set)
>     (pattys, cs)  <- runWriterT $ mapM (checkPat (s ::: sty)) pats
>     modifyContext (<><< map Constraint cs)
>     ty'     <- simplifyTy <$> generalise sty
>     modifyContext (:< Func s ty')
>     return $ FunDecl s (Just ty') (map tmOf pattys)
> checkFunDecl (FunDecl s (Just st) pats@(Pat xs _ _ : _)) = 
>   inLocation ("in declaration of " ++ s) $ do
>     modifyContext (:< Layer FunTop)
>     sty ::: k <- inLocation ("in type " ++ show (prettyHigh st)) $ inferKind B0 st
>     unless (k == Set) $ errKindNotSet k
>     (pattys, cs) <- runWriterT $ mapM (checkPat (s ::: sty)) pats
>     let ty = tyOf (head pattys)
>     modifyContext (<><< map Constraint cs)
>     ty' <- simplifyTy <$> generalise ty
>     (ty'', cs') <- runWriterT $ instantiate ty'
>     sty' <- specialise sty
>     inLocation ("when matching inferred type\n        " ++ show (prettyFst ty')
>         ++ "\n    against given type\n        " ++ show (prettyFst sty)) $
>             unify ty'' sty'
>     inLocation ("when solving predicates") $ solvePreds False cs'
>     modifyContext (:< Func s ty')
>     return (FunDecl s (Just sty) (map tmOf pattys))
> checkFunDecl (FunDecl s _ []) =
>   inLocation ("in declaration of " ++ s) $ fail $ "No alternative"



> checkPat :: String ::: Type -> Pat String String ->
>     ContextualWriter [Predicate] () (Pattern ::: Type)
> checkPat (s ::: sty) (Pat xs g t) =
>   inLocation ("in alternative " ++ s ++ " " ++ show (prettyHigh (Pat xs g t))) $ do
>     (xs', (bs, ps)) <- lift $ runWriterT $ checkPatTerms xs
>     modifyContext (:< Layer (PatternTop (s ::: sty) bs ps []))
>     t' ::: tty  <- infer t
>     sty'        <- instantiate sty
>     let  xtms ::: xtys  = unzipAsc xs'
>          ty             = xtys /-> tty
>     lift $ unify ty sty'
>     cs <- lift extractPatConstraints
>     mtrace $ "checkPat extracted constraints: " ++ show cs
>     return $ Pat xtms Trivial t' ::: ty

> extractPatConstraints :: Contextual t [Predicate]
> extractPatConstraints = getContext >>= flip help []
>   where
>     help (g :< Layer (PatternTop _ _ _ cs)) h = putContext (g <><< h) >> return cs
>     help (g :< a) h = help g (a : h)


> checkPatTerm :: PatTerm String String ->
>     ContextualWriter ([TmName ::: Type], [Predicate]) () (PatternTerm ::: Type)
> checkPatTerm (PatVar v) = do
>     vty <- TyVar <$> fresh ("_ty" ++ v) (Hole ::: Set)
>     tell ([v ::: vty], [])
>     return $ PatVar v ::: vty
> checkPatTerm (PatCon c pts) = do
>     sc   <- lookupTmCon c
>     cty  <- mapPatWriter $ instantiate sc
>     unless (length pts == args cty) $
>         errConUnderapplied c (args cty) (length pts)
>     ptms ::: ptys  <- unzipAsc <$> checkPatTerms pts
>     cod            <- TyVar <$> fresh "_cod" (Hole ::: Set)
>     lift $ unify cty $ ptys /-> cod
>     return $ PatCon c ptms ::: cod
>   where
>     mapPatWriter w = mapWriterT (\ xcs -> xcs >>= \ (x, cs) -> return (x, ([], cs))) w


> checkPatTerms = mapM checkPatTerm