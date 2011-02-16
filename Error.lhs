> {-# LANGUAGE TypeSynonymInstances, FlexibleContexts, GADTs, TypeOperators,
>              NoMonomorphismRestriction #-}

> module Error where

> import qualified Control.Monad.Error as E
> import Text.PrettyPrint.HughesPJ

> import TyNum
> import Type
> import Kit
> import Syntax
> import PrettyPrinter

> data Err a x where
>     MissingTyVar       :: String -> Err a x
>     MissingNumVar      :: String -> Err a x
>     MissingTyCon       :: String -> Err a x
>     MissingTmVar       :: String -> Err a x
>     MissingTmCon       :: String -> Err a x
>     KindTarget         :: Kind -> Err a x
>     KindNot            :: Kind -> String -> Err a x
>     KindMismatch       :: Ty a ::: Kind -> Kind -> Err a x
>     ConstructorTarget  :: Ty a -> Err a x
>     ConUnderapplied    :: TmConName -> Int -> Int -> Err a x
>     DuplicateTyCon     :: TyConName -> Err a x
>     DuplicateTmCon     :: TmConName -> Err a x
>     NonNumericVar      :: a -> Err a x
>     CannotUnify        :: Ty a -> Ty a -> Err a x
>     UnifyFixed         :: a -> Ty a -> Err a x
>     UnifyNumFixed      :: a -> TyNum a -> Err a x         
>     Fail               :: String -> Err a x

> instance Pretty Error where
>     pretty (MissingTyVar a)       _ = text $ "Missing type variable " ++ a
>     pretty (MissingNumVar a)      _ = text $ "Missing numeric type variable " ++ a
>     pretty (MissingTyCon a)       _ = text $ "Missing type constructor " ++ a
>     pretty (MissingTmVar a)       _ = text $ "Missing term variable " ++ a
>     pretty (MissingTmCon a)       _ = text $ "Missing data constructor " ++ a
>     pretty (KindTarget k)         _ = text "Kind" <+> prettyHigh k <+> text "doesn't target *"
>     pretty (KindNot k s)          _ = text "Kind" <+> prettyHigh k <+> text "is not" <+> text s
>     pretty (KindMismatch (t ::: k) l) _ = text "Kind" <+> prettyHigh k
>         <+> text "of" <+> prettyFst t <+> text "is not" <+> prettyHigh l
>     pretty (ConstructorTarget t)  _ = text "Type" <+> prettyFst t <+>
>                                           text "doesn't target data type"
>     pretty (ConUnderapplied c n m)  _ = text $ "Constructor " ++ c ++ " should have "
>         ++ show n ++ " arguments, but has been given " ++ show m
>     pretty (DuplicateTyCon t) _ = text $ "Duplicate type constructor " ++ t
>     pretty (DuplicateTmCon t) _ = text $ "Duplicate data constructor " ++ t
>     pretty (NonNumericVar a) _ = text $ "Type variable " ++ fst a ++ " is not numeric"
>     pretty (CannotUnify t u) _ = text "Cannot unify"
>         <+> prettyFst t <+> text "and" <+> prettyFst u
>     pretty (UnifyFixed a t) _ = text "Cannot unify fixed variable" <+> text (fst a) 
>         <+> text "with" <+> prettyFst t
>     pretty (UnifyNumFixed a n) _ = text "Cannot modify fixed variable"
>         <+> text (fst a) <+> text "to unify" <+> prettyFst n <+> text "with 0"
>     pretty (Fail s) _ = text s

> throw :: (E.MonadError ErrorData m) => Error -> m a
> throw e = E.throwError (e, [] :: [String])

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
                            

> type Error = Err TyName TmName
> type ErrorData = (Error, [String])

> instance E.Error ErrorData where
>     noMsg     = (Fail "Unknown error", [])
>     strMsg s  = (Fail s, [])

> instance Pretty ErrorData where
>     pretty (e, ss) _ = hang (prettyHigh e) 4 (vcat $ reverse $ map prettyHigh ss)



> inLocation :: (E.MonadError ErrorData m) => String -> m a -> m a
> inLocation s m = m `E.catchError` (\ (e, ss) -> E.throwError (e, s:ss))

> inLoc :: (E.MonadError ErrorData m) => m a -> m String -> m a
> inLoc m ms = m `E.catchError` (\ (e, ss) -> ms >>= \ s -> E.throwError (e, s:ss))