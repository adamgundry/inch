> {-# LANGUAGE TypeSynonymInstances #-}

> module PrettyContext where

> import Text.PrettyPrint.HughesPJ

> import Kit
> import Type
> import PrettyPrinter
> import Context

> instance PrettyVar a => Pretty (TyEnt a) where
>     pretty (a := d ::: k) _ = prettyVar a <+> text ":="
>       <+> prettyHigh d <+> text ":" <+> prettyHigh k

> instance (Show a, Show x, PrettyVar a, PrettyVar x) => Pretty (Ent a x) where
>   pretty (A a) _ = prettyHigh a
>   pretty (Layer l)    _ = prettyHigh l
>   pretty (Func f ty)  _ = prettyVar f <+> text "::" <+> prettyHigh ty
>   pretty (Constraint Given p)   _ = braces (prettyHigh p) <> text "!!"
>   pretty (Constraint Wanted p)  _ = braces (prettyHigh p) <> text "??"

> instance PrettyVar a => Pretty (TyDef a) where
>   pretty Hole _ = text "?"
>   pretty Fixed _ = text "!"
>   pretty (Some t) _ = prettyHigh t

> instance (Show a, Show x, PrettyVar x, PrettyVar a) => Pretty (TmLayer a x) where
>   pretty (PatternTop (s ::: sty) bs ps cs) _ = text "<PatternTop>"
>       $$ prettyVar s <+> text "::" <+> prettyHigh sty
>       $$ brackets (fsep $ punctuate (text ",") $ map (\ (x ::: ty) -> prettyVar x <+> text "::" <+> prettyHigh ty) bs)
>       $$ braces (fsepPretty ps) <> text "!"
>       $$ braces (fsepPretty cs) <> text "?"
>       $$ text "</PatternTop>"
>   pretty l _ = text (show l)