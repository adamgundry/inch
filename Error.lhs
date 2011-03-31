> {-# LANGUAGE TypeSynonymInstances, FlexibleContexts, GADTs, TypeOperators,
>              NoMonomorphismRestriction #-}

> module Error where

> import Data.List
> import qualified Control.Monad.Error as E
> import Text.PrettyPrint.HughesPJ

> import TyNum
> import Type
> import Kit
> import Syntax
> import PrettyPrinter

> data Err k a x where
>     MissingTyVar       :: String -> Err k a x
>     MissingNumVar      :: String -> Err k a x
>     MissingTyCon       :: String -> Err k a x
>     MissingTmVar       :: String -> Err k a x
>     MissingTmCon       :: String -> Err k a x
>     KindTarget         :: k -> Err k a x
>     KindNot            :: k -> String -> Err k a x
>     KindMismatch       :: Ty k a ::: k -> k -> Err k a x
>     ConstructorTarget  :: Ty k a -> Err k a x
>     ConUnderapplied    :: TmConName -> Int -> Int -> Err k a x
>     DuplicateTyCon     :: TyConName -> Err k a x
>     DuplicateTmCon     :: TmConName -> Err k a x
>     NonNumericVar      :: a -> Err k a x
>     CannotUnify        :: Ty k a -> Ty k a -> Err k a x
>     UnifyFixed         :: a -> Ty k a -> Err k a x
>     UnifyNumFixed      :: a -> TyNum a -> Err k a x
>     CannotDeduce       :: [NormPred a] -> [NormPred a] -> Err k a x
>     BadExistential     :: a -> Ty k a -> [Pat k a x] -> Err k a x
>     Fail               :: String -> Err k a x

> instance Pretty Error where
>     pretty (MissingTyVar a)            _ = text $ "Missing type variable " ++ a
>     pretty (MissingNumVar a)           _ = text $ "Missing numeric type variable " ++ a
>     pretty (MissingTyCon a)            _ = text $ "Missing type constructor " ++ a
>     pretty (MissingTmVar a)            _ = text $ "Missing term variable " ++ a
>     pretty (MissingTmCon a)            _ = text $ "Missing data constructor " ++ a
>     pretty (KindTarget k)              _ = text "Kind" <+> prettyHigh k <+> text "doesn't target *"
>     pretty (KindNot k s)               _ = text "Kind" <+> prettyHigh k <+> text "is not" <+> text s
>     pretty (KindMismatch (t ::: k) l)  _ = text "Kind" <+> prettyHigh k <+> text "of" <+> prettyHigh t <+> text "is not" <+> prettyHigh l
>     pretty (ConstructorTarget t)       _ = text "Type" <+> prettyHigh t <+> text "doesn't target data type"
>     pretty (ConUnderapplied c n m)     _ = text $ "Constructor " ++ c ++ " should have " ++ show n ++ " arguments, but has been given " ++ show m
>     pretty (DuplicateTyCon t)          _ = text $ "Duplicate type constructor " ++ t
>     pretty (DuplicateTmCon t)          _ = text $ "Duplicate data constructor " ++ t
>     pretty (NonNumericVar a)           _ = text "Type variable" <+> prettyVar a <+> text "is not numeric"
>     pretty (CannotUnify t u)           _ = sep  [  text "Cannot unify"
>                                                 ,  nest 2 (prettyHigh t)
>                                                 ,  text "with"
>                                                 ,  nest 2 (prettyHigh u)
>                                                 ]
>     pretty (UnifyFixed a t)            _ = text "Cannot unify fixed variable" <+> prettyVar a <+> text "with" <+> prettyHigh t
>     pretty (UnifyNumFixed a n)         _ = text "Cannot modify fixed variable" <+> prettyVar a <+> text "to unify" <+> prettyHigh n <+> text "with 0"
>     pretty (CannotDeduce [] qs)        _ = sep  [  text "Could not deduce"
>                                                 ,  nest 2 (fsepPretty (nub qs))
>                                                 ,  text "in empty context"
>                                                 ]
>     pretty (CannotDeduce hs qs)        _ = sep  [  text "Could not deduce"
>                                                 ,  nest 2 (fsepPretty (nub qs))
>                                                 ,  text "from hypotheses"
>                                                 ,  nest 2 (fsepPretty (nub hs))
>                                                 ]
>     pretty (BadExistential a t ps)     _ = sep  [  text "Illegal existential"
>                                                        <+> prettyVar a
>                                                 ,  text "when generalising type"
>                                                 ,  nest 2 (prettyHigh t)
>                                                 ,  text "and patterns"
>                                                 ,  nest 2 (vcatPretty ps)
>                                                 ]
>     pretty (Fail s)                    _ = text s

> throw :: (E.MonadError ErrorData m) => Error -> m a
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
> errNonNumericVar a        = throw (NonNumericVar a)
> errCannotUnify t u        = throw (CannotUnify t u)
> errUnifyFixed a t         = throw (UnifyFixed a t)
> errUnifyNumFixed a n      = throw (UnifyNumFixed a n)
> errCannotDeduce hs qs     = throw (CannotDeduce hs qs)
> errBadExistential a t ps  = throw (BadExistential a t ps)
                            

> type Error = Err Kind TyName TmName
> type ErrorData = (Error, [Doc])

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