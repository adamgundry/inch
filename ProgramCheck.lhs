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
>     solvePreds False cs'
>     modifyContext (:< Func s ty')
>     return (FunDecl s (Just sty) (map tmOf pattys))
> checkFunDecl (FunDecl s _ []) =
>   inLocation ("in declaration of " ++ s) $ fail $ "No alternative"



> checkPat :: String ::: Type -> Pat String String ->
>     ContextualWriter [Predicate] () (Pattern ::: Type)
> checkPat (s ::: sty) (Pat xs g t) =
>   inLocation ("in alternative " ++ s ++ " " ++ show (prettyHigh (Pat xs g t))) $ do
>     (ps, (btys, cs)) <- lift $ runWriterT $ checkPatTerms xs
>     tell cs
>     modifyContext (:< Layer (PatternTop (s ::: sty) btys))
>     t' ::: ty <- infer t
>     let g' = Trivial -- nonsense
>     let oty = foldr (-->) ty (map tyOf ps)
>     sty' <- instantiate sty
>     lift $ unify oty sty'
>     return $ Pat (fmap tmOf ps) g' t' ::: oty

> checkPatTerms = mapM checkPatTerm

> checkPatTerm :: PatTerm String String ->
>     ContextualWriter ([TmName ::: Type], [Predicate]) () (PatternTerm ::: Type)
> checkPatTerm (PatVar v) = do
>     nm <- fresh ("_ty" ++ v) (Hole ::: Set)
>     tell ([v ::: TyVar nm], [])
>     return $ PatVar v ::: TyVar nm
> checkPatTerm (PatCon c pts) = do
>     sc <- lookupTmCon c
>     ty <- mapPatWriter $ instantiate sc
>     unless (length pts == args ty) $ errConUnderapplied c (args ty) (length pts)
>     pts' <- checkPatTerms pts
>     nm <- fresh "_s" (Hole ::: Set)
>     lift $ unify ty $ foldr (-->) (TyVar nm) (map tyOf pts')
>     return $ PatCon c (map tmOf pts') ::: TyVar nm
>   where
>     mapPatWriter w = mapWriterT (\ xcs -> xcs >>= \ (x, cs) -> return (x, ([], cs))) w