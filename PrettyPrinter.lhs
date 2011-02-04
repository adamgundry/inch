> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

> module PrettyPrinter where

> import Text.PrettyPrint.HughesPJ

> import Syntax


> data Size = ArgSize | AppSize | LamSize
>     deriving (Bounded, Eq, Ord, Show)

> class Pretty x where
>     pretty :: x -> Size -> Doc


> prettyLow :: Pretty x => x -> Doc
> prettyLow = flip pretty minBound

> prettyHigh :: Pretty x => x -> Doc
> prettyHigh = flip pretty maxBound

> wrapDoc :: Size -> Doc -> Size -> Doc
> wrapDoc dSize d curSize
>   | dSize > curSize  = parens d
>   | otherwise        = d


> instance Pretty String where
>     pretty s _ = text s


> instance Pretty Kind where
>     pretty Set         = const $ text "*"
>     pretty NatKind     = const $ text "Nat"
>     pretty (k ::-> l)  = wrapDoc AppSize $
>                              pretty k ArgSize <+> text "->"
>                                  <+> pretty l AppSize

> instance Pretty a => Pretty (Ty a) where
>     pretty (TyVar a)  = pretty a
>     pretty (TyCon c)  = pretty c
>     pretty (s :-> t)  = wrapDoc AppSize $ 
>         pretty s ArgSize <+> text "->" <+> pretty t AppSize
>     pretty (Pi a k t)  = wrapDoc AppSize $ text "pi"
>         <+> parens (prettyHigh a <+> text "::" <+> prettyHigh k)
>         <+> text "." <+> pretty t AppSize
>     pretty (All a k t)  = wrapDoc AppSize $ text "forall"
>         <+> parens (prettyHigh a <+> text "::" <+> prettyHigh k)
>         <+> text "." <+> pretty t AppSize

> instance Pretty a => Pretty (Tm a) where
>     pretty (TmVar x)  = pretty x
>     pretty (TmCon s)  = pretty s
>     pretty (Lam x t)  = wrapDoc LamSize $
>         text "\\" <+> prettyHigh x <+> text "->" <+> pretty t AppSize
>     pretty (f :$ a)   = wrapDoc AppSize $
>         pretty f AppSize <+> pretty a ArgSize
>     pretty (t :? ty)  = wrapDoc AppSize $ 
>         pretty t AppSize <+> text "::" <+> pretty ty AppSize

> instance Pretty a => Pretty (Decl a) where
>     pretty (DataDecl n k cs) _ = hang (text "data" <+> pretty n ArgSize
>         <+> (if k /= Set then text "::" <+> pretty k ArgSize else empty)
>         <+> text "where") 2 $
>             vcat (map prettyHigh cs)
>     pretty (FunDecl n Nothing ps) _ = vcat (map ((prettyHigh n <+>) . prettyHigh) ps)


> instance Pretty a => Pretty (Con a) where
>     pretty (Con s ty) _ = pretty s ArgSize <+> text "::" <+> pretty ty ArgSize

> instance Pretty a => Pretty (Pat a) where
>     pretty (Pat vs Trivial e) _ = hsep (map prettyHigh vs) <+> text "="
>                                       <+> prettyHigh e

> instance Pretty a => Pretty (PatTerm a) where
>     pretty p = pretty (patToTm p)



> instance Pretty Program where
>     pretty p _ = vcat (map prettyHigh p)