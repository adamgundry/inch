> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

> module PrettyPrinter where

> import Data.Foldable
> import Data.List
> import Text.PrettyPrint.HughesPJ
> import Data.Bifunctor

> import BwdFwd hiding ((<+>))
> import Syntax
> import Kit


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

> prettyProgram :: Program -> Doc
> prettyProgram = prettyHigh . map (bimap fst id)


> instance Pretty String where
>     pretty s _ = text s


> instance Pretty Kind where
>     pretty Set            = const $ text "*"
>     pretty KindNum        = const $ text "Num"
>     pretty (KindArr k l)  = wrapDoc AppSize $
>         pretty k ArgSize <+> text "->" <+> pretty l AppSize

> instance Pretty Binder where
>     pretty Pi _   = text "pi"
>     pretty All _  = text "forall"

> instance Pretty (TyNum String) where
>     pretty (NumConst k) = const $ integer k
>     pretty (NumVar a) = pretty a
>     pretty (m :+: Neg n) = wrapDoc AppSize $ 
>         pretty m ArgSize <+> text "-" <+> pretty n ArgSize
>     pretty (m :+: n) = wrapDoc AppSize $ 
>         pretty m ArgSize <+> text "+" <+> pretty n ArgSize
>     pretty (m :*: n) = wrapDoc AppSize $ 
>         pretty m ArgSize <+> text "*" <+> pretty n ArgSize
>     pretty (Neg n) = wrapDoc AppSize $
>         text "-" <+> pretty n ArgSize

> instance Pretty (Ty String) where
>     pretty (TyVar a)                = pretty a
>     pretty (TyCon c)                = pretty c
>     pretty (TyApp (TyApp Arr s) t)  = wrapDoc ArrSize $ 
>         pretty s AppSize <+> text "->" <+> pretty t ArrSize
>     pretty (TyApp f s)  = wrapDoc AppSize $ 
>         pretty f AppSize <+> pretty s ArgSize
>     pretty Arr          = const (parens (text "->"))
>     pretty (TyNum n) = pretty n
>     pretty (Bind b a k t) = prettyBind b (B0 :< (a, k)) $
>                                 alphaConvert [(a, a ++ "'")] (unbind a t)

> prettyBind :: Binder -> Bwd (String, Kind) -> Ty String -> Size -> Doc
> prettyBind b bs (Bind b' a k t) | b == b' = prettyBind b (bs :< (a, k)) $
>     alphaConvert [(a, a ++ "'")] (unbind a t)
> prettyBind b bs t = wrapDoc LamSize $ prettyHigh b
>         <+> prettyBits (trail bs)
>         <+> text "." <+> pretty t ArrSize
>   where
>     prettyBits []             = empty
>     prettyBits ((a, k) : aks) = prettyRun k empty ((a, k) : aks)
>     prettyRun l d ((a, k) : aks) | k == l = prettyRun l (d <+> text a) aks
>     prettyRun Set  d aks = d <+> prettyBits aks
>     prettyRun l    d aks = parens (d <+> text "::" <+> prettyHigh l) <+> prettyBits aks

> instance Pretty (Tm String String) where
>     pretty (TmVar x)  = pretty x
>     pretty (TmCon s)  = pretty s
>     pretty (TmApp f s)   = wrapDoc AppSize $
>         pretty f AppSize <+> pretty s ArgSize
>     pretty (Lam x t)  = prettyLam (text x) (unbind x t)
>     pretty (t :? ty)  = wrapDoc ArrSize $ 
>         pretty t AppSize <+> text "::" <+> pretty ty maxBound

> prettyLam :: Doc -> Tm String String -> Size -> Doc
> prettyLam d (Lam x t) = prettyLam (d <+> text x) (unbind x t)
> prettyLam d t = wrapDoc LamSize $
>         text "\\" <+> d <+> text "->" <+> pretty t AppSize

> instance Pretty (Decl String String) where
>     pretty (DD d) = pretty d 
>     pretty (FD f) = pretty f

> instance Pretty (DataDecl String String) where
>     pretty (DataDecl n k cs) _ = hang (text "data" <+> prettyHigh n
>         <+> (if k /= Set then text "::" <+> prettyHigh k else empty)
>         <+> text "where") 2 $
>             vcat (map prettyHigh cs)

> instance Pretty (FunDecl String String) where
>     pretty (FunDecl n Nothing ps) _ = vcat (map ((prettyHigh n <+>) . prettyHigh) ps)
>     pretty (FunDecl n (Just ty) ps) _ = vcat $ (prettyHigh n <+> text "::" <+> prettyHigh ty) : map ((prettyHigh n <+>) . prettyHigh) ps


> instance Pretty (Con String) where
>     pretty (s ::: ty) _ = prettyHigh s <+> text "::" <+> prettyHigh ty

> instance Pretty (Pat String String) where
>     pretty (Pat vs Trivial e) _ = hsep (map prettyLow vs) <+> text "="
>                                       <+> prettyHigh e

> instance Pretty (PatTerm String String) where
>     pretty p = pretty (patToTm p)



> instance Pretty (Prog String String) where
>     pretty p _ = vcat (intersperse (text " ") $ map prettyHigh p)
