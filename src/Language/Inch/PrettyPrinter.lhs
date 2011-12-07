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
> import Language.Inch.ModuleSyntax
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

> prettyVar :: Var () k -> Doc
> prettyVar = prettyHigh . fogVar

> prettySysVar :: Var () k -> Doc
> prettySysVar = prettyHigh . fogSysVar

> prettyFog :: (TravTypes1 t, Pretty (t RAW ())) => t OK () -> Doc
> prettyFog = prettyHigh . fog1

> prettyFogSys :: (TravTypes1 t, Pretty (t RAW ())) => t OK () -> Doc
> prettyFogSys = prettyHigh . fogSys

> renderMe :: Pretty a => a -> String
> renderMe x = renderStyle style{ribbonsPerLine=1.2, lineLength=80} (prettyHigh x)

> (<++>) :: Doc -> Doc -> Doc
> d1 <++> d2 = sep [d1, nest 2 d2]
> infix 2 <++>


> instance Pretty String where
>     pretty s _ = text s

> instance Pretty [STopDeclaration] where
>     pretty ds _ = vcat (map prettyHigh ds)

> instance Pretty SKind where
>     pretty SKSet       = const $ text "*"
>     pretty SKNum       = const $ text "Integer"
>     pretty SKNat       = const $ text "Nat"
>     pretty SKConstraint = const $ text "Constraint"
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
>     pretty (STyComp c)      = const . parens $ prettyHigh c
 
> infixName :: SType -> Maybe String
> infixName SArr                       = Just "->"
> infixName (SBinOp o) | binOpInfix o  = Just (binOpString o)
> infixName (STyCon ('(':s))           = Just (init s)
> infixName (STyComp c)                = Just (show (prettyHigh c))
> infixName _                          = Nothing


> prettyBind :: Binder -> Bwd (String, SKind) ->
>     SType -> Size -> Doc
> prettyBind b bs (SBind b' a k t) | b == b' = prettyBind b (bs :< (a, k)) t
> -- prettyBind b (bs :< (a, SKNum)) (SQual (P LE 0 (STyVar a')) t) | a == a' = prettyBind b (bs :< (a, SKNat)) t
> prettyBind b bs t = wrapDoc LamSize $ prettyHigh b
>         <+> prettyBits (trail bs)
>         <+> text "." <++> pretty t ArrSize
>   where
>     prettyBits []             = empty
>     prettyBits ((a, SKSet) : aks) = text a <+> prettyBits aks
>     prettyBits ((a, k) : aks) = parens (text a <+> text "::" <+> prettyHigh k) <+> prettyBits aks


> prettyQual :: Bwd SType -> SType -> Size -> Doc
> prettyQual ps (SQual p t) = prettyQual (ps :< p) t
> prettyQual ps t = wrapDoc ArrSize $
>     prettyPreds (trail ps) <+> text "=>" <++> pretty t ArrSize
>   where
>     prettyPreds xs = parens (hsep (punctuate (text ",") (map prettyHigh xs)))


> instance Pretty (STerm a) where
>     pretty (TmVar x)    = const $ text x
>     pretty (TmCon s)    = const $ text s
>     pretty (TmInt k)    = wrapDoc (if k < 0 then ArrSize else minBound) $
>                               integer k
>     pretty (CharLit c)  = const $ text $ show c
>     pretty (StrLit s)   = const $ text $ show s
>     -- pretty (TmApp (TmApp f m) n) | Just s <- infixTmName f =
>     --    wrapDoc AppSize $ pretty m ArgSize <+> text s <+> pretty n ArgSize
>     pretty (TmApp f s)  = wrapDoc AppSize $
>         pretty f AppSize <++> pretty s ArgSize
>     pretty (TmBrace n)  = const $ braces $ prettyHigh n 
>     pretty (Lam x t)    = prettyLam (text x) t
>     pretty (NumLam x t) = prettyLam (braces (text x)) t
>     pretty (Let ds t)   = wrapDoc maxBound $ text "let" <+> vcatSpacePretty ds $$ text "in" <+> prettyHigh t
>     pretty (Case t as)  = wrapDoc maxBound $ text "case" <+> prettyHigh t <+> text "of" <++> vcatPretty as
>     pretty (t :? ty)    = wrapDoc ArrSize $ 
>         pretty t AppSize <+> text "::" <+> pretty ty maxBound

> infixTmName :: STerm a -> Maybe String
> infixTmName (TmVar ('(':v)) = Just (init v)
> infixTmName _ = Nothing

> prettyLam :: Doc -> STerm a -> Size -> Doc
> prettyLam d (Lam x t) = prettyLam (d <+> text x) t
> prettyLam d (NumLam a t) = prettyLam (d <+> braces (text a)) t
> prettyLam d t = wrapDoc LamSize $
>         text "\\" <+> d <+> text "->" <+> pretty t AppSize


> parenCommaList :: Doc -> [String] -> Doc
> parenCommaList _ [] = empty
> parenCommaList d xs = d <+> parens (hsep (punctuate (text ",") (map text xs)))


> instance Pretty SModule where
>     pretty (Mod mh is ds) _ = maybe empty prettyModHeader mh
>                                   $$ vcat (map prettyHigh is)
>                                   $$ vcat (intersperse (text " ") (map prettyHigh ds))
>       where
>         prettyModHeader (s, es) = text "module" <+> text s <+> parenCommaList empty es <+> text "where"


> instance Pretty Import where
>     pretty (Import q n as imp) _ = text "import"
>                                            <+> (if q then text "qualified" else empty)
>                                            <+> text n
>                                            <+> (maybe empty (\ s -> text "as" <+> text s) as)
>                                            <+> prettyHigh imp

> instance Pretty ImpSpec where
>     pretty ImpAll          _ = empty
>     pretty (Imp xs)        _ = parens (hsep (punctuate (text ",") (map text xs)))
>     pretty (ImpHiding xs)  _ = text "hiding" <+> parens (hsep (punctuate (text ",") (map text xs)))


> instance Pretty STypeSyn where
>     pretty (SSynTy t)      _ = text "=" <+> prettyHigh t
>     pretty (SSynAll x k t) _ = kindBracket k <+> prettyHigh t
>       where
>         kindBracket SKSet  = text x
>         kindBracket l      = parens (text x <+> text "::" <+> prettyHigh l)

> instance Pretty STopDeclaration where
>     pretty (DataDecl n k cs ds) _ = hang (text "data" <+> text n
>         <+> (if k /= SKSet then text "::" <+> prettyHigh k else empty)
>         <+> text "where") 2 $
>             vcat (map prettyHigh cs) $$ derivingClause ds
>       where
>         derivingClause []  = empty
>         derivingClause xs  = text "deriving" <+>
>                                parens (hsep (punctuate  (text ",") (map text xs)))
>     pretty (TypeDecl x t) _ = text "type" <+> text x <+> prettyHigh t
>     pretty (CDecl x (ClassDecl vs ss ms)) _ =
>         hang (text "class"
>               <+> (if null ss then empty else parens (fsepPretty ss) <+> text "=>")
>               <+> text x <+> fsep (map prettyHigh vs)
>               <+> text "where") 2 $
>                   vcat (map prettyHigh ms)
>     pretty (IDecl x (InstDecl ts cs zs)) _ =
>         hang (text "instance"
>               <+> (if null cs then empty else parens (fsepPretty cs) <+> text "=>")
>               <+> text x  <+> fsep (map prettyHigh ts)
>               <+> text "where") 2 $
>                   vcat (map (prettyHigh . uncurry FunDecl) zs)
>     pretty (Decl d) s = pretty d s

> instance Pretty (SDeclaration a) where
>     pretty (FunDecl n ps) _ = vcat (map ((text n <+>) . prettyHigh) ps)
>     pretty (SigDecl n ty) _ = text n <+> text "::" <+> prettyHigh ty


> instance (Pretty x, Pretty p) => Pretty (x ::: p) where
>   pretty (x ::: p) _ = prettyHigh x <+> text "::" <+> prettyHigh p



> instance Pretty (SCaseAlternative a) where
>     pretty (CaseAlt v gt) _ = prettyHigh v <+> prettyGuardTerms (text "->") gt

> instance Pretty (SAlternative a) where
>     pretty (Alt vs gt) _ = prettyLow vs <+> prettyGuardTerms (text "=") gt


> prettyGuardTerms :: Doc -> SGuardTerms a -> Doc
> prettyGuardTerms d (Unguarded e ds) = d <++> prettyHigh e $$ prettyWhere ds
> prettyGuardTerms d (Guarded gts ds) =
>     vcat (map (\ (g :*: e) -> text "|" <+> prettyLow g <+> d <+> prettyHigh e) gts)
>     $$ prettyWhere ds

> prettyWhere :: [SDeclaration a] -> Doc 
> prettyWhere []  = empty
> prettyWhere ds  = text "where" <+> vcat (map prettyHigh ds)



> instance Pretty (SPatternList a b) where
>     pretty P0         _  = empty
>     pretty (p :! ps)  z  = pretty p z <+> pretty ps z

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
>     pretty (PatIntLit i)   = const $ integer i
>     pretty (PatCharLit c)  = const $ text $ show c
>     pretty (PatStrLit s)   = const $ text $ show s
>     pretty (PatNPlusK n k) = const $ parens $ text n <+> text "+" <+> integer k

> instance Pretty (SGuard a) where
>     pretty (ExpGuard t)  = const $ fsepPretty t
>     pretty (NumGuard p)  = const $ braces (fsepPretty p)


> instance Pretty (VarList RAW a b) where
>     pretty P0         _  = empty
>     pretty (p :! ps)  z  = pretty p z <+> pretty ps z

> instance Pretty (VarBinding RAW a b) where
>     pretty (VB x SKSet) _ = prettyHigh x
>     pretty (VB x k)     _ = parens (prettyHigh x <+> text "::" <+> prettyHigh k)

> instance Pretty (TyList RAW a b) where
>     pretty P0               _  = empty
>     pretty (TyK t _ :! ps)  z  = pretty t z <+> pretty ps z

> instance Pretty (VarKind RAW ()) where
>     pretty (VK v _) = pretty v

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


> fsepPretty :: Pretty a => [a] -> Doc
> fsepPretty xs  = fsep . punctuate (text ",") . map prettyHigh $ xs

> vcatSpacePretty :: Pretty a => [a] -> Doc
> vcatSpacePretty xs  = vcat . intersperse (text " ") . map prettyHigh $ xs

> vcatPretty :: Pretty a => [a] -> Doc
> vcatPretty xs  = vcat . map prettyHigh $ xs