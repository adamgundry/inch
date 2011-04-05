> {-# LANGUAGE TypeSynonymInstances #-}

> module PrettyContext where

> import Text.PrettyPrint.HughesPJ

> import Kit
> import Kind
> import Type
> import TyNum
> import PrettyPrinter
> import Context

> instance Pretty (TyEntry k) where
>     pretty (a := d) _ = prettyHigh a <+> text ":="
>       <+> prettyHigh d <+> text ":" <+> prettyHigh (fogKind (varKind a))

> instance Pretty Entry where
>   pretty (A a) _ = prettyHigh a
>   pretty (Layer l)    _ = prettyHigh l
>   pretty (Func f ty)  _ = prettyHigh f <+> text "::" <+> prettyHigh (fogTy ty)
>   pretty (Constraint Given p)   _ = braces (prettyHigh p) <> text "!!"
>   pretty (Constraint Wanted p)  _ = braces (prettyHigh p) <> text "??"

> instance Pretty (TyDef k) where
>   pretty Hole      _ = text "?"
>   pretty Fixed     _ = text "!"
>   pretty Exists    _ = text "Ex"
>   pretty (Some t)  l = pretty (fogTy t) l

> instance Pretty TmLayer where
>   pretty _ _ = text "TmLayer"
> {-
>   pretty (PatternTop ssty bs ps cs) _ = text "<PatternTop>"
>       $$ prettyHigh (fogTy ssty)
>       $$ brackets (fsepPretty (map fog bs))
>       $$ braces (fsepPretty (map fog ps)) <> text "!"
>       $$ braces (fsepPretty (map fog cs)) <> text "?"
>       $$ text "</PatternTop>"
>   pretty (LetBody bs ()) _ = text "<LetBody>" $$ vcatPretty (map fog bs) $$ text "</LetBody>"
> -}