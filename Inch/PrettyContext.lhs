> {-# LANGUAGE TypeSynonymInstances #-}

> module PrettyContext where

> import Text.PrettyPrint.HughesPJ

> import Kit
> import Kind
> import Type
> import PrettyPrinter
> import Context

> instance Pretty (TyEntry k) where
>     pretty (a := d) _ = prettySysVar a <+> text ":="
>       <+> prettyHigh d <+> text ":" <+> prettyHigh (fogKind (varKind a))

> instance Pretty Entry where
>   pretty (A a)                  _ = prettyHigh a
>   pretty (Layer l)              _ = prettyHigh l
>   pretty (Constraint Given p)   _ =
>       braces (prettyHigh $ fogSysPred p) <> text "!!"
>   pretty (Constraint Wanted p)  _ =
>       braces (prettyHigh $ fogSysPred p) <> text "??"

> instance Pretty (TyDef k) where
>   pretty Hole      _ = text "?"
>   pretty Fixed     _ = text "!"
>   pretty Exists    _ = text "Ex"
>   pretty (Some t)  l = pretty (fogSysTy t) l

> instance Pretty TmLayer where
>   pretty l = const $ text $ show l