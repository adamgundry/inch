> {-# LANGUAGE TypeSynonymInstances, FlexibleContexts, GADTs #-}

> module Error where

> import qualified Control.Monad.Error as E
> import Text.PrettyPrint.HughesPJ

> import Syntax
> import PrettyPrinter

> data Err a x where
>     MissingTyVar       :: String -> Err a x
>     MissingNumVar      :: String -> Err a x
>     MissingTyCon       :: String -> Err a x
>     MissingTmVar       :: String -> Err a x
>     MissingTmCon       :: String -> Err a x
>     KindTarget         :: Kind -> Err a x
>     KindNotSet         :: Kind -> Err a x
>     ConstructorTarget  :: Ty a -> Err a x
>     ConUnderapplied    :: String -> Int -> Int -> Err a x
>     Fail               :: String -> Err a x

> instance Pretty Error where
>     pretty (MissingTyVar a)       _ = text $ "Missing type variable " ++ a
>     pretty (MissingNumVar a)      _ = text $ "Missing numeric type variable " ++ a
>     pretty (MissingTyCon a)       _ = text $ "Missing type constructor " ++ a
>     pretty (MissingTmVar a)       _ = text $ "Missing term variable " ++ a
>     pretty (MissingTmCon a)       _ = text $ "Missing data constructor " ++ a
>     pretty (KindTarget k)         _ = text "Kind" <+> prettyHigh k <+> text "doesn't target *"
>     pretty (KindNotSet k)         _ = text "Kind" <+> prettyHigh k <+> text "is not *"
>     pretty (ConstructorTarget t)  _ = text "Type" <+> prettyFst t <+>
>                                           text "doesn't target data type"
>     pretty (ConUnderapplied c n m)  _ = text $ "Constructor " ++ c ++ " should have "
>         ++ show n ++ " arguments, but has been given " ++ show m
>     pretty (Fail s) _ = text s

> throw :: (E.MonadError ErrorData m) => Error -> m a
> throw e = E.throwError (e, [] :: [String])

> missingTyVar a          = throw (MissingTyVar a)
> missingNumVar a         = throw (MissingNumVar a)
> missingTyCon a          = throw (MissingTyCon a)
> missingTmVar a          = throw (MissingTmVar a)
> missingTmCon a          = throw (MissingTmCon a)
> errKindTarget k         = throw (KindTarget k)
> errKindNotSet k         = throw (KindNotSet k)
> errConstructorTarget t  = throw (ConstructorTarget t)
> errConUnderapplied c n m  = throw (ConUnderapplied c n m)


> type Error = Err TyName TmName
> type ErrorData = (Error, [String])

> instance E.Error ErrorData where
>     noMsg     = (Fail "Unknown error", [])
>     strMsg s  = (Fail s, [])

> instance Pretty ErrorData where
>     pretty (e, ss) _ = hang (prettyHigh e) 4 (vcat $ reverse $ map prettyHigh ss)



> inLocation :: (E.MonadError ErrorData m) => String -> m a -> m a
> inLocation s m = m `E.catchError` (\ (e, ss) -> E.throwError (e, s:ss))