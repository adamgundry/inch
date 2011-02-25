> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts #-}

> module ProgramCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Maybe
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
> import PrettyContext
> import KindCheck
> import TypeCheck


> typeCheck p = runStateT (checkProg p) initialState

> checkProg :: SProgram -> Contextual () Program
> checkProg = mapM checkDecl 

> checkDecl :: SDeclaration -> Contextual () Declaration
> checkDecl (DD d) = DD <$> checkDataDecl d
> checkDecl (FD f) = FD <$> checkFunDecl f
>     

> checkDataDecl :: SDataDeclaration -> Contextual () DataDeclaration
> checkDataDecl (DataDecl t k cs) = inLocation ("in data type " ++ t) $ do
>     unless (targetsSet k) $ errKindTarget k
>     insertTyCon t k
>     DataDecl t k <$> mapM (checkConstructor t) cs

> checkConstructor :: TyConName -> SConstructor -> Contextual () Constructor
> checkConstructor t (c ::: ty) = inLocation ("in constructor " ++ c) $ do
>     (ty' ::: k) <- inferKind B0 ty
>     unless (k == Set) $ errKindNotSet k
>     unless (ty' `targets` t) $ errConstructorTarget ty'
>     insertTmCon c ty'
>     return (c ::: ty')


> checkFunDecl :: SFunDeclaration -> Contextual () FunDeclaration

> checkFunDecl (FunDecl s Nothing pats@(Pat xs _ _ : _)) =
>   inLocation ("in declaration of " ++ s) $ do
>     modifyContext (:< Layer FunTop)
>     sty     <- unknownTyVar $ "sty" ::: Set
>     pattys  <- mapM (checkPat (s ::: sty)) pats
>     mtrace . (s ++) . (" checkFunDecl context: " ++) . render =<< getContext
>     ty'     <- simplifyTy <$> generalise sty
>     modifyContext (:< Func s ty')
>     return $ FunDecl s (Just ty') (map tmOf pattys)

> checkFunDecl (FunDecl s (Just st) pats@(Pat xs _ _ : _)) = 
>   inLocation ("in declaration of " ++ s) $ do
>     modifyContext (:< Layer FunTop)
>     sty ::: k <- inLocation ("in type " ++ render st) $ inferKind B0 st
>     unless (k == Set) $ errKindNotSet k
>     pattys <- mapM (checkPat (s ::: sty)) pats
>     let ty = tyOf (head pattys)
>     -- mtrace . (s ++) . (" checkFunDecl context: " ++) . render =<< getContext
>     ty' <- simplifyTy <$> generalise ty
>     -- mtrace $ "checkFunDecl ty': " ++ render ty'
>     sty'  <- specialise sty
>     ty''  <- instantiate ty'

>     -- mtrace . ("checkFunDecl pre-match: " ++) . render =<< getContext
>     inLocation ("when matching inferred type\n        " ++ render ty'
>         ++ "\n    against given type\n        " ++ render sty) $ do
>             unify ty'' sty'
>             inLocation ("when solving constraints") $ unifySolveConstraints >> solveConstraints False
>     modifyContext $ (:< Func s sty) . dropToDecl
>     return (FunDecl s (Just sty) (map tmOf pattys))

> checkFunDecl (FunDecl s _ []) =
>   inLocation ("in declaration of " ++ s) $ fail $ "No alternative"


> dropToDecl :: Context -> Context
> dropToDecl (g :< Layer FunTop)  = g
> dropToDecl (g :< e)             = dropToDecl g


> checkPat :: String ::: Type -> SPattern -> Contextual () (Pattern ::: Type)
> checkPat (s ::: sty) (Pat xs g t) =
>   inLocation ("in alternative " ++ s ++ " " ++ show (prettyHigh (Pat xs g t))) $ do
>     sty'        <- specialise sty
>     (xs', (bs, ps)) <- runWriterT $ checkPatTerms xs
>     modifyContext (:< Layer (PatternTop (s ::: sty) bs ps []))
>     t' ::: tty  <- infer t
>     let  xtms ::: xtys  = unzipAsc xs'
>          ty             = xtys /-> tty
>     unify ty sty'
>     mtrace . (s ++) . (" checkPat context: " ++) . render =<< getContext
>     unifySolveConstraints
>     solveConstraints True
>
>     -- mtrace . (s ++) . (" checkPat context: " ++) . show . prettyHigh =<< getContext
>     mtrace . (s ++) . (" checkPat ty: " ++) . render =<< niceType ty
>     return $ Pat xtms Trivial t' ::: ty

> unifySolveConstraints :: Contextual t ()
> unifySolveConstraints = do
>     ns <- collectEqualities <$> getContext
>     mapM_ (unifyZero F0) ns
>   where
>     collectEqualities :: Context -> [NormalNum]
>     collectEqualities B0 = []
>     collectEqualities (g :< Constraint Wanted (IsZero n)) = n : collectEqualities g
>     collectEqualities (g :< _) = collectEqualities g

> checkPatTerm :: SPatternTerm ->
>     ContextualWriter ([TmName ::: Type], [NormalPredicate]) () (PatternTerm ::: Type)
> checkPatTerm (PatVar v) = do
>     vty <- unknownTyVar $ "_ty" ++ v ::: Set
>     tell ([v ::: vty], [])
>     return $ PatVar v ::: vty
> checkPatTerm (PatCon c pts) = do
>     sc   <- lookupTmCon c
>     cty  <- mapPatWriter $ inst Hole sc
>     unless (length pts == args cty) $
>         errConUnderapplied c (args cty) (length pts)
>     ptms ::: ptys  <- unzipAsc <$> checkPatTerms pts
>     cod            <- unknownTyVar $ "_cod" ::: Set
>     lift $ unify cty $ ptys /-> cod
>     return $ PatCon c ptms ::: cod
>   where
>     mapPatWriter w = mapWriterT (\ xcs -> xcs >>= \ (x, cs) -> return (x, ([], cs))) w


> checkPatTerms = mapM checkPatTerm
