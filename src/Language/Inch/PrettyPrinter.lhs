> {-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts,
>              TypeOperators, GADTs, PatternGuards #-}

> module Language.Inch.PrettyPrinter where

> import Data.Foldable
> import Data.List
> import Text.PrettyPrint.HughesPJ

> import Language.Inch.Kind
> import Language.Inch.Type
> import Language.Inch.BwdFwd
> import Language.Inch.Syntax
> import Language.Inch.Kit


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
> prettyProgram = prettySProgram . map fog

> prettySProgram :: SProgram -> Doc
> prettySProgram = vcat . intersperse (text " ") . map prettyHigh

> prettyVar :: Var () k -> Doc
> prettyVar = prettyHigh . fogVar

> prettySysVar :: Var () k -> Doc
> prettySysVar = prettyHigh . fogSysVar

> prettyFog :: (TravTypes t, Pretty (t RAW ())) => t OK () -> Doc
> prettyFog = prettyHigh . fog

> prettyFogSys :: (TravTypes t, Pretty (t RAW ())) => t OK () -> Doc
> prettyFogSys = prettyHigh . fogSys

> renderMe :: Pretty a => a -> String
> renderMe x = renderStyle style{ribbonsPerLine=1.2, lineLength=80} (prettyHigh x)

> d1 <++> d2 = sep [d1, nest 2 d2]
> infix 2 <++>


> instance Pretty String where
>     pretty s _ = text s


> instance Pretty SKind where
>     pretty SKSet       = const $ text "*"
>     pretty SKNum       = const $ text "Num"
>     pretty SKNat       = const $ text "Nat"
>     pretty (k :--> l)  = wrapDoc AppSize $
>         pretty k ArgSize <+> text "->" <+> pretty l AppSize

> instance Pretty Binder where
>     pretty Pi _   = text "pi"
>     pretty All _  = text "forall"

> instance Pretty ty => Pretty (Pred ty) where
>     pretty (P c n m) = wrapDoc AppSize $
>         pretty n ArgSize <+> pretty c ArgSize <+> pretty m ArgSize
>     pretty (p :=> q) = wrapDoc AppSize $ 
>         pretty p ArgSize <+> text "=>" <++> pretty q ArgSize

> instance Pretty Comparator where
>     pretty LS _ = text "<"
>     pretty LE _ = text "<=" 
>     pretty GR _ = text ">"
>     pretty GE _ = text ">="
>     pretty EL _ = text "~"

> instance Pretty UnOp where
>     pretty o _ = text $ unOpString o

> instance Pretty BinOp where
>     pretty o _ | binOpInfix o  = text $ "(" ++ binOpString o ++ ")"
>                | otherwise     = text $ binOpString o

> instance Pretty SType where
>     pretty (STyVar v)                  = const $ text v
>     pretty (STyCon c)                  = const $ text c
>     pretty (STyApp (STyCon l) t) | l == listTypeName  = const $ brackets (prettyHigh t)
>     pretty (STyApp (STyApp (STyCon c) s) t) | c == tupleTypeName = const $ parens (prettyHigh s <> text "," <+> prettyHigh t)
>     pretty (STyApp (STyApp f s) t) | Just fx <- infixName f = wrapDoc ArrSize $ 
>         pretty s AppSize <+> text fx <++> pretty t AppSize
>     pretty (STyApp f s)  = wrapDoc AppSize $ 
>         pretty f AppSize <+> pretty s ArgSize
>     pretty (SBind b a k t)  = prettyBind b (B0 :< (a, k)) t
>     pretty (SQual p t)      = prettyQual (B0 :< p) t
>     pretty SArr             = const $ text "(->)"
>     pretty (STyInt k)       = wrapDoc (if k < 0 then ArrSize else minBound) $
>                                   integer k
>     pretty (SBinOp o)       = pretty o
>     pretty (SUnOp o)        = pretty o
 
> infixName :: SType -> Maybe String
> infixName SArr                       = Just "->"
> infixName (SBinOp o) | binOpInfix o  = Just (binOpString o)
> infixName (STyCon ('(':s))           = Just (init s)
> infixName _                          = Nothing


> prettyBind :: Binder -> Bwd (String, SKind) ->
>     SType -> Size -> Doc
> prettyBind b bs (SBind b' a k t) | b == b' = prettyBind b (bs :< (a, k)) t
> prettyBind b (bs :< (a, SKNum)) (SQual (P LE 0 (STyVar a')) t) | a == a' = prettyBind b (bs :< (a, SKNat)) t
> prettyBind b bs t = wrapDoc LamSize $ prettyHigh b
>         <+> prettyBits (trail bs)
>         <+> text "." <++> pretty t ArrSize
>   where
>     prettyBits []             = empty
>     prettyBits ((a, SKSet) : aks) = text a <+> prettyBits aks
>     prettyBits ((a, k) : aks) = parens (text a <+> text "::" <+> prettyHigh k) <+> prettyBits aks


> prettyQual :: Bwd SPredicate -> SType -> Size -> Doc
> prettyQual ps (SQual p t) = prettyQual (ps :< p) t
> prettyQual ps t = wrapDoc ArrSize $
>     prettyPreds (trail ps) <+> text "=>" <++> pretty t ArrSize
>   where
>     prettyPreds ps = hsep (punctuate (text ",") (map prettyHigh ps))


> instance Pretty (STerm a) where
>     pretty (TmVar x)    = const $ text x
>     pretty (TmCon s)    = const $ text s
>     pretty (TmInt k)    = wrapDoc (if k < 0 then ArrSize else minBound) $
>                               integer k
>     pretty (TmApp (TmApp (TmBinOp o) m) n) | binOpInfix o =
>         wrapDoc AppSize $ pretty m ArgSize <+> text (binOpString o) <+> pretty n ArgSize
>     pretty (TmApp f s)  = wrapDoc AppSize $
>         pretty f AppSize <++> pretty s ArgSize
>     pretty (TmBrace n)  = const $ braces $ prettyHigh n 
>     pretty (Lam x t)    = prettyLam (text x) t
>     pretty (NumLam x t) = prettyLam (braces (text x)) t
>     pretty (Let ds t)   = wrapDoc maxBound $ text "let" <+> vcatSpacePretty ds $$ text "in" <+> prettyHigh t
>     pretty (Case t as)  = wrapDoc maxBound $ text "case" <+> prettyHigh t <+> text "of" <++> vcatPretty as
>     pretty (t :? ty)    = wrapDoc ArrSize $ 
>         pretty t AppSize <+> text "::" <+> pretty ty maxBound
>     pretty (TmUnOp o)   = pretty o
>     pretty (TmBinOp o)  = pretty o

> prettyLam :: Doc -> STerm a -> Size -> Doc
> prettyLam d (Lam x t) = prettyLam (d <+> text x) t
> prettyLam d (NumLam a t) = prettyLam (d <+> braces (text a)) t
> prettyLam d t = wrapDoc LamSize $
>         text "\\" <+> d <+> text "->" <+> pretty t AppSize

> instance Pretty (SDeclaration a) where
>     pretty (DataDecl n k cs ds) _ = hang (text "data" <+> text n
>         <+> (if k /= SKSet then text "::" <+> prettyHigh k else empty)
>         <+> text "where") 2 $
>             vcat (map prettyHigh cs) $$ derivingClause ds
>       where
>         derivingClause []  = empty
>         derivingClause ds  = text "deriving" <+> parens (hsep (punctuate  (text ",") (map text ds)))
>     pretty (FunDecl n ps) _ = vcat (map ((text n <+>) . prettyHigh) ps)
>     pretty (SigDecl n ty) _ = text n <+> text "::" <+> prettyHigh ty


> instance (Pretty x, Pretty p) => Pretty (x ::: p) where
>   pretty (x ::: p) _ = prettyHigh x <+> text "::" <+> prettyHigh p



> instance Pretty (SCaseAlternative a) where
>     pretty (CaseAlt v gt) _ = prettyHigh v <+> prettyGuardTerms (text "->") gt

> instance Pretty (SAlternative a) where
>     pretty (Alt vs gt) _ = prettyLow vs <+> prettyGuardTerms (text "=") gt


> prettyGuardTerms :: Doc -> SGuardTerms a -> Doc
> prettyGuardTerms d (Unguarded e) = d <++> prettyHigh e
> prettyGuardTerms d (Guarded gts) =
>     vcat $ map (\ (g :*: e) -> text "|" <+> prettyLow g <+> d <++> prettyHigh e) gts



> instance Pretty (SPatternList a b) where
>     pretty P0 z = empty
>     pretty (p :! ps) z = pretty p z <+> pretty ps z

> instance Pretty (SPattern a b) where
>     pretty (PatVar x)    = const $ text x
>     pretty (PatCon c P0) = const $ text c
>     pretty (PatCon "+" (a :! b:! P0)) = wrapDoc AppSize $
>         prettyLow a <+> text "+" <+> prettyLow b
>     pretty (PatCon c ps) = wrapDoc AppSize $
>                                text c <+> prettyLow ps
>     pretty PatIgnore = const $ text "_"
>     pretty (PatBraceK k)   = const $ braces $ integer k
>     pretty (PatBrace a 0)  = const $ braces $ text a
>     pretty (PatBrace a k)  = const $ braces $
>                                     text a <+> text "+" <+> integer k

> instance Pretty (SGuard a) where
>     pretty (ExpGuard t)  = pretty t
>     pretty (NumGuard p)  = const $ braces (fsepPretty p)


> {-
> instance Pretty SNormalPred where
>     pretty p = pretty (reifyPred p)

> instance Pretty SNormalNum where
>     pretty n _ = prettyHigh $ reifyNum n
> -}

> instance Pretty x => Pretty (Bwd x) where
>     pretty bs _ = fsep $ punctuate (text ",") (map prettyHigh (trail bs))

> instance Pretty x => Pretty (Fwd x) where
>     pretty bs _ = fsep $ punctuate (text ",") $ map prettyHigh $ Data.Foldable.foldr (:) [] bs


> fsepPretty xs  = fsep . punctuate (text ",") . map prettyHigh $ xs
> vcatSpacePretty xs  = vcat . intersperse (text " ") . map prettyHigh $ xs
> vcatPretty xs  = vcat . map prettyHigh $ xs