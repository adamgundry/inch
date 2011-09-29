> {-# LANGUAGE TypeSynonymInstances, FlexibleContexts, GADTs, TypeOperators,
>              NoMonomorphismRestriction #-}

> module Error where

> import Data.List
> import qualified Control.Monad.Error as E
> import Text.PrettyPrint.HughesPJ

> import Kind
> import Type
> import Kit
> import Syntax
> import PrettyPrinter

> data Err where
>     MissingTyVar       :: String -> Err
>     MissingNumVar      :: String -> Err
>     MissingTyCon       :: String -> Err
>     MissingTmVar       :: String -> Err
>     MissingTmCon       :: String -> Err
>     KindTarget         :: SKind -> Err
>     KindNot            :: SKind -> String -> Err
>     KindMismatch       :: SType ::: SKind -> SKind -> Err
>     ConstructorTarget  :: SType -> Err
>     ConUnderapplied    :: TmConName -> Int -> Int -> Err
>     DuplicateTyCon     :: TyConName -> Err
>     DuplicateTmCon     :: TmConName -> Err
>     DuplicateTmVar     :: TmName -> Err
>     NonNumericVar      :: Ex (Var ()) -> Err
>     CannotUnify        :: SType -> SType -> Err
>     UnifyFixed         :: Ex (Var ()) -> Ex (Ty ()) -> Err
>     UnifyNumFixed      :: NVar () -> Ty () KNum -> Err
>     CannotDeduce       :: [NormalPredicate] -> [NormalPredicate] -> Err
>     BadExistential     :: Ex (Var ()) -> Ex (Ty ()) -> [Alternative ()] -> Err
>     ImpossiblePred     :: NormalPredicate -> Err
>     BadBindingLevel    :: Var () KNum -> Err
>     Fail               :: String -> Err

> instance Pretty Err where
>     pretty (MissingTyVar a)   _ = text $ "Missing type variable " ++ a
>     pretty (MissingNumVar a)  _ = text $ "Missing numeric type variable " ++ a
>     pretty (MissingTyCon a)   _ = text $ "Missing type constructor " ++ a
>     pretty (MissingTmVar a)   _ = text $ "Missing term variable " ++ a
>     pretty (MissingTmCon a)   _ = text $ "Missing data constructor " ++ a
>     pretty (KindTarget k)     _ = text "Kind" <+> prettyHigh k <+> text "doesn't target *"
>     pretty (KindNot k s)      _ = text "Kind" <+> prettyHigh k <+> text "is not" <+> text s
>     pretty (KindMismatch (t ::: k) l)  _ = text "Kind" <+> prettyHigh k <+> text "of" <+> prettyHigh t <+> text "is not" <+> prettyHigh l
>     pretty (ConstructorTarget t)       _ = text "Type" <+> prettyHigh t <+> text "doesn't target data type"
>     pretty (ConUnderapplied c n m)     _ = text $ "Constructor " ++ c ++ " should have " ++ show n ++ " arguments, but has been given " ++ show m
>     pretty (DuplicateTyCon t)          _ = text $ "Duplicate type constructor " ++ t
>     pretty (DuplicateTmCon t)          _ = text $ "Duplicate data constructor " ++ t
>     pretty (DuplicateTmVar t)          _ = text $ "Duplicate term variable " ++ t
>     pretty (NonNumericVar (Ex a))      _ = text "Type variable" <+> prettySysVar a <+> text "is not numeric"
>     pretty (CannotUnify t u)           _ = sep  [  text "Cannot unify"
>                                                 ,  nest 2 (prettyHigh t)
>                                                 ,  text "with"
>                                                 ,  nest 2 (prettyHigh u)
>                                                 ]
>     pretty (UnifyFixed (Ex a) (Ex t))  _ = text "Cannot unify fixed variable" <+> prettySysVar a <+> text "with" <+> prettyHigh (fogSysTy t)
>     pretty (UnifyNumFixed a n)         _ = text "Cannot modify fixed variable" <+> prettySysVar a <+> text "to unify" <+> prettyHigh (fogSysTy n) <+> text "with 0"
>     pretty (CannotDeduce [] qs)        _ = sep  [  text "Could not deduce"
>                                                 ,  nest 2 (fsepPretty $ map (fogSysPred . reifyPred) $ nub qs)
>                                                 ,  text "in empty context"
>                                                 ]
>     pretty (CannotDeduce hs qs)        _ = sep  [  text "Could not deduce"
>                                                 ,  nest 2 (fsepPretty $ map (fogSysPred . reifyPred) $ nub qs)
>                                                 ,  text "from hypotheses"
>                                                 ,  nest 2 (fsepPretty $ map (fogSysPred . reifyPred) $ nub hs)
>                                                 ]
>     pretty (BadExistential (Ex a) (Ex t) as)  _ = sep  [  text "Illegal existential"
>                                                        <+> prettySysVar a
>                                                 ,  text "when generalising type"
>                                                 ,  nest 2 (prettyHigh $ fogSysTy t)
>                                                 ,  text "and patterns"
>                                                 ,  nest 2 (vcatPretty $ fmap fogSys as)
>                                                 ]
>     pretty (ImpossiblePred p) _ = text "Impossible constraint " <+> prettyHigh (fogSysPred $ reifyPred p)
>     pretty (BadBindingLevel a) _ = text "Forall-bound variable"
>                                        <+> prettyVar a
>                                        <+> text "used where pi-bound variable required"
>     pretty (Fail s)           _ = text s

> throw :: (E.MonadError ErrorData m) => Err -> m a
> throw e = E.throwError (e, [] :: [Doc])

> missingTyVar a            = throw (MissingTyVar a)
> missingNumVar a           = throw (MissingNumVar a)
> missingTyCon a            = throw (MissingTyCon a)
> missingTmVar a            = throw (MissingTmVar a)
> missingTmCon a            = throw (MissingTmCon a)
> errKindTarget k           = throw (KindTarget k)
> errKindNotSet k           = throw (KindNot k "*")
> errKindNotArrow k         = throw (KindNot k "an arrow")
> errKindMismatch tk l      = throw (KindMismatch tk l)
> errConstructorTarget t    = throw (ConstructorTarget t)
> errConUnderapplied c n m  = throw (ConUnderapplied c n m)
> errDuplicateTyCon t       = throw (DuplicateTyCon t)
> errDuplicateTmCon t       = throw (DuplicateTmCon t)
> errDuplicateTmVar t       = throw (DuplicateTmVar t)
> errNonNumericVar a        = throw (NonNumericVar (Ex a))
> errCannotUnify t u        = throw (CannotUnify t u)
> errUnifyFixed a t         = throw (UnifyFixed (Ex a) (Ex t))
> errUnifyNumFixed a n      = throw (UnifyNumFixed a n)
> errCannotDeduce hs qs     = throw (CannotDeduce hs qs)
> errBadExistential a t ps  = throw (BadExistential (Ex a) (Ex t) ps)
> errImpossiblePred p       = throw (ImpossiblePred p)
> errBadBindingLevel a      = throw (BadBindingLevel a)                            


> type ErrorData = (Err, [Doc])

> instance E.Error ErrorData where
>     noMsg     = (Fail "Unknown error", [])
>     strMsg s  = (Fail s, [])

> instance Pretty ErrorData where
>     pretty (e, ss) _ = hang (prettyHigh e) 4 (vcat $ reverse ss)



> inLocation :: (E.MonadError ErrorData m) => Doc -> m a -> m a
> inLocation s m = m `E.catchError` (\ (e, ss) -> E.throwError (e, s:ss))

> inLoc :: (E.MonadError ErrorData m) => m a -> m Doc -> m a
> inLoc m ms = m `E.catchError` (\ (e, ss) -> ms >>= \ s -> E.throwError (e, s:ss))


> erk :: (E.MonadError ErrorData m) => String -> m a
> erk s = E.throwError (Fail s, [])