> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

> module PrettyPrinter where

> import Data.Foldable
> import Data.List
> import Text.PrettyPrint.HughesPJ

> import BwdFwd hiding ((<+>))
> import Syntax


> data Size = ArgSize | AppSize | ArrSize | LamSize
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
>     pretty Set            = const $ text "*"
>     pretty KindNat        = const $ text "Nat"
>     pretty (KindArr k l)  = wrapDoc AppSize $
>         pretty k ArgSize <+> text "->" <+> pretty l AppSize

> instance Pretty Binder where
>     pretty Pi _   = text "pi"
>     pretty All _  = text "forall"

> instance Pretty (Ty String) where
>     pretty (TyVar a)                = pretty a
>     pretty (TyCon c)                = pretty c
>     pretty (TyApp (TyApp Arr s) t)  = wrapDoc ArrSize $ 
>         pretty s AppSize <+> text "->" <+> pretty t ArrSize
>     pretty (TyApp f s)  = wrapDoc AppSize $ 
>         pretty f AppSize <+> pretty s ArgSize
>     pretty Arr          = const (parens (text "->"))
>     pretty (Bind b a k t) = prettyBind b (B0 :< (a, k)) $
>                                 alphaConvert [(a, a ++ "'")] (unbind a t)

> prettyBind :: Binder -> Bwd (String, Kind) -> Ty String -> Size -> Doc
> prettyBind b bs (Bind b' a k t) | b == b' = prettyBind b (bs :< (a, k)) (unbind a t)
> prettyBind b bs t = wrapDoc ArrSize $ prettyHigh b
>         <+> prettyBits (trail bs)
>         <+> text "." <+> pretty t ArrSize
>   where
>     prettyBits []             = empty
>     prettyBits ((a, k) : aks) = prettyRun k empty ((a, k) : aks)
>     prettyRun l d ((a, k) : aks) | k == l = prettyRun l (d <+> text a) aks
>     prettyRun Set  d aks = d <+> prettyBits aks
>     prettyRun l    d aks = parens (d <+> text "::" <+> prettyHigh l) <+> prettyBits aks

> instance Pretty (Tm String) where
>     pretty (TmVar x)  = pretty x
>     pretty (TmCon s)  = pretty s
>     pretty (TmApp f s)   = wrapDoc AppSize $
>         pretty f AppSize <+> pretty s ArgSize
>     pretty (Lam x t)  = wrapDoc LamSize $
>         text "\\" <+> prettyHigh x <+> text "->" <+> pretty (unbind x t) AppSize
>     pretty (t :? ty)  = wrapDoc AppSize $ 
>         pretty t AppSize <+> text "::" <+> pretty ty AppSize

> instance Pretty (Decl String) where
>     pretty (DD d) = pretty d 
>     pretty (FD f) = pretty f

> instance Pretty (DataDecl String) where
>     pretty (DataDecl n k cs) _ = hang (text "data" <+> prettyHigh n
>         <+> (if k /= Set then text "::" <+> prettyHigh k else empty)
>         <+> text "where") 2 $
>             vcat (map prettyHigh cs)

> instance Pretty (FunDecl String) where
>     pretty (FunDecl n Nothing ps) _ = vcat (map ((prettyHigh n <+>) . prettyHigh) ps)
>     pretty (FunDecl n (Just ty) ps) _ = vcat $ (prettyHigh n <+> text "::" <+> prettyHigh ty) : map ((prettyHigh n <+>) . prettyHigh) ps


> instance Pretty (Con String) where
>     pretty (Con s ty) _ = prettyHigh s <+> text "::" <+> prettyHigh ty

> instance Pretty (Pat String) where
>     pretty (Pat vs Trivial e) _ = hsep (map prettyLow vs) <+> text "="
>                                       <+> prettyHigh e

> instance Pretty (PatTerm String) where
>     pretty p = pretty (patToTm p)



> instance Pretty (Prog String) where
>     pretty p _ = vcat (intersperse (text " ") $ map prettyHigh p)

> instance Pretty Program where
>     pretty p _ = vcat (intersperse (text " ") $ map prettyHigh p)

> instance (Functor f, Pretty (f String))
>              => Pretty (f (String, a)) where
>    pretty x = pretty (fmap fst x)