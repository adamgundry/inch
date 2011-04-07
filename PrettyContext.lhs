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
>     pretty (a := d) _ = prettySysVar a <+> text ":="
>       <+> prettyHigh d <+> text ":" <+> prettyHigh (fogKind (varKind a))

> instance Pretty Entry where
>   pretty (A a)                  _ = prettyHigh a
>   pretty (Layer l)              _ = prettyHigh l
>   pretty (Constraint Given p)   _ =
>       braces (prettyHigh $ fogSysPred $ reifyPred p) <> text "!!"
>   pretty (Constraint Wanted p)  _ =
>       braces (prettyHigh $ fogSysPred $ reifyPred p) <> text "??"

> instance Pretty (TyDef k) where
>   pretty Hole      _ = text "?"
>   pretty Fixed     _ = text "!"
>   pretty Exists    _ = text "Ex"
>   pretty (Some t)  l = pretty (fogSysTy t) l

> instance Pretty TmLayer where
>   pretty (PatternTop (x ::: _) _ _ _)  _ = text $ "PatternTop " ++ x
>   pretty (AppLeft _ _ _)               _ = text "AppLeft"
>   pretty (AppRight _ _)                _ = text "AppRight"
>   pretty (LamBody (x ::: _) _)         _ = text $ "LamBody " ++ x
>   pretty (LetBody _ _)                 _ = text "LetBody"
>   pretty (AnnotLeft _ _)               _ = text "AnnotLeft"
>   pretty FunTop                        _ = text "FunTop"
>   pretty GenMark                       _ = text "GenMark"

> {-
>   pretty (PatternTop ssty bs ps cs) _ = text "<PatternTop>"
>       $$ prettyHigh (fogTy ssty)
>       $$ brackets (fsepPretty (map fog bs))
>       $$ braces (fsepPretty (map fog ps)) <> text "!"
>       $$ braces (fsepPretty (map fog cs)) <> text "?"
>       $$ text "</PatternTop>"
>   pretty (LetBody bs ()) _ = text "<LetBody>" $$ vcatPretty (map fog bs) $$ text "</LetBody>"
> -}