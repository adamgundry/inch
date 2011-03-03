> {-# LANGUAGE GADTs, TypeOperators, FlexibleContexts #-}

> module ProgramCheck where

> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import Control.Monad.Writer hiding (All)
> import Data.List
> import Data.Maybe
> import Data.Traversable

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
> checkProg xs = do
>     let (ds, _) = partitionDecls xs
>     traverse makeTyCon ds
>     traverse checkDecl xs
>   where
>     makeTyCon :: SDataDeclaration -> Contextual () ()
>     makeTyCon (DataDecl t k cs) = inLocation ("in data type " ++ t) $ do
>         unless (targetsSet k) $ errKindTarget k
>         insertTyCon t k

> checkDecl :: SDeclaration -> Contextual () Declaration
> checkDecl (DD d) = DD <$> checkDataDecl d
> checkDecl (FD f) = FD <$> checkFunDecl f  

> checkDataDecl :: SDataDeclaration -> Contextual () DataDeclaration
> checkDataDecl (DataDecl t k cs) = inLocation ("in data type " ++ t) $
>     DataDecl t k <$> traverse (checkConstructor t) cs

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
>     pattys  <- traverse (checkPat True (s ::: sty) sty) pats
>     -- mtrace . (s ++) . (" checkFunDecl context: " ++) . render =<< getContext
>     ty'     <- simplifyTy <$> generalise sty
>     modifyContext (:< Func s ty')
>     return $ FunDecl s (Just ty') (map tmOf pattys)

> checkFunDecl (FunDecl s (Just st) pats@(Pat xs _ _ : _)) = 
>   inLocation ("in declaration of " ++ s) $ do
>     modifyContext (:< Layer FunTop)
>     sty ::: k <- inLocation ("in type " ++ render st) $ inferKind B0 st
>     unless (k == Set) $ errKindNotSet k

>     sty'  <- specialise sty

>     pattys <- traverse (checkPat False (s ::: sty) sty') pats
>     let ty = tyOf (head pattys)
>     -- mtrace . (s ++) . (" checkFunDecl context: " ++) . render . expandContext =<< getContext
>     ty' <- simplifyTy <$> generalise ty
>     -- mtrace $ "checkFunDecl ty': " ++ render ty'

> {-
>     sty''  <- specialise sty
>     ty''   <- instantiate ty'

>     -- mtrace . ("checkFunDecl pre-match: " ++) . render =<< getContext
>     inLocation ("when matching inferred type\n        " ++ render ty'
>         ++ "\n    against given type\n        " ++ render sty) $ do
>             unify ty'' sty''
>             inLocation ("when solving constraints") $ unifySolveConstraints >> solveConstraints False
> -}
> 
>     modifyContext $ (:< Func s sty) . dropToDecl
>     return (FunDecl s (Just sty) (map tmOf pattys))

> checkFunDecl (FunDecl s _ []) =
>   inLocation ("in declaration of " ++ s) $ fail $ "No alternative"


> dropToDecl :: Context -> Context
> dropToDecl (g :< Layer FunTop)  = g
> dropToDecl (g :< e)             = dropToDecl g


> checkPat :: Bool -> String ::: Type -> Type -> SPattern -> Contextual () (Pattern ::: Type)
> checkPat try (s ::: sc) sty (Pat xs g t) =
>   inLocation ("in alternative " ++ s ++ " " ++ render (Pat xs g t)) $ do
>     ((xs', rty), (bs, ps)) <- runWriterT $ checkPatTerms sty xs
>     rty <- specialise rty
>     modifyContext (:< Layer (PatternTop (s ::: sc) bs ps []))
>     t' ::: tty  <- infer t
>     let  xtms ::: xtys  = unzipAsc xs'
>          ty             = xtys /-> tty

>     -- nty <- niceType ty
>     -- nsty <- niceType sty
>     -- mtrace $ "checkPat unifying: " ++ render nty ++ " and " ++ render nsty

>     unify tty rty
>     -- mtrace . (s ++) . (" checkPat context: " ++) . render . expandContext =<< getContext
>     unifySolveConstraints
>     solveConstraints try
>
>     -- mtrace . (s ++) . (" checkPat context: " ++) . show . prettyHigh =<< getContext
>     -- mtrace . (s ++) . (" checkPat ty: " ++) . render =<< niceType ty
>     return $ Pat xtms Trivial t' ::: ty

> matchArity :: Type -> [SPatternTerm] -> Contextual t ([SPatternTerm ::: Type], Type)
> matchArity t [] = return ([], t)
> matchArity (TyApp (TyApp (TyB Arr) s) t) (x:xs) = do
>     (ys, ty) <- matchArity t xs
>     return ((x ::: s):ys, ty)
> matchArity (Bind Pi y KindNum t) (x:xs) = do
>     beta <- fresh y (Fixed ::: KindNum)
>     (ys, ty) <- matchArity (unbind beta t) xs
>     return ((x ::: TyB NumTy):ys, ty)
> matchArity t (x:xs) = do
>     sv <- unknownTyVar $ "_sv" ::: Set
>     tv <- unknownTyVar $ "_tv" ::: Set
>     unify t (sv --> tv)
>     (ys, ty) <- matchArity tv xs
>     return ((x ::: sv):ys, ty)

> unifySolveConstraints :: Contextual t ()
> unifySolveConstraints = do
>     ns <- collectEqualities <$> getContext
>     traverse (unifyZero F0) ns
>     return ()
>   where
>     collectEqualities :: Context -> [NormalNum]
>     collectEqualities B0 = []
>     collectEqualities (g :< Constraint Wanted (IsZero n)) = n : collectEqualities g
>     collectEqualities (g :< _) = collectEqualities g


> checkPatTerms :: Type -> [SPatternTerm] ->
>     ContextualWriter ([TmName ::: Type], [NormalPredicate]) ()
>     ([PatternTerm ::: Type], Type)
> checkPatTerms t [] = return ([], t)
> checkPatTerms sat (PatVar v : ps) = do
>     (s, t) <- lift $ splitFun sat
>     tell ([v ::: s], [])
>     (pts, ty) <- checkPatTerms t ps
>     return ((PatVar v ::: s) : pts, ty)
> checkPatTerms sat (PatCon c xs : ps) =
>   inLocation ("in pattern " ++ render (PatCon c xs)) $ do
>     (s, t) <- lift $ splitFun sat
>     sc   <- lookupTmCon c
>     cty  <- mapPatWriter $ inst Hole sc
>     unless (length xs == args cty) $
>         errConUnderapplied c (args cty) (length xs)
>     (pts, aty)  <- checkPatTerms cty xs
>     lift $ unify s aty
>     (pps, ty) <- checkPatTerms t ps
>     return ((PatCon c (map tmOf pts) ::: s) : pps, ty)
>   where
>     mapPatWriter w = mapWriterT (\ xcs -> xcs >>= \ (x, cs) -> return (x, ([], cs))) w

> checkPatTerms sat (PatIgnore : ps) = do
>     (s, t) <- lift $ splitFun sat
>     (pts, ty) <- checkPatTerms t ps
>     return ((PatIgnore ::: s) : pts, ty)

> checkPatTerms (Bind Pi x KindNum t) (PatBrace Nothing k : ps) = do
>     nm <- fresh x (Fixed ::: KindNum)
>     tell ([], [IsZero (mkVar nm -~ mkConstant k)])
>     (pts, ty) <- checkPatTerms (unbind nm t) ps
>     return ((PatBrace Nothing k ::: TyNum (NumVar nm)) : pts, ty)

> checkPatTerms (Bind Pi x KindNum t) (PatBrace (Just a) k : ps) = do
>     nm <- fresh (x ++ "oo") (Fixed ::: KindNum)
>     am <- fresh a (Fixed ::: KindNum)
>     tell ([], [IsPos (mkVar am), IsZero (mkVar nm -~ (mkVar am +~ mkConstant k))])
>     (pts, ty) <- checkPatTerms (unbind nm t) ps
>     return ((PatBrace (Just a) k ::: TyNum (NumVar nm)) : pts, ty)


> splitFun :: Type -> Contextual t (Type, Type)
> splitFun (TyApp (TyApp (TyB Arr) s) t) = return (s, t)
> splitFun (Qual q t) = do
>     q' <- normalisePred q
>     modifyContext (:< Constraint Given q')
>     splitFun t

> splitFun t = do
>     a <- unknownTyVar $ "_dom" ::: Set
>     b <- unknownTyVar $ "_cod" ::: Set
>     unify (a --> b) t
>     return (a, b)
