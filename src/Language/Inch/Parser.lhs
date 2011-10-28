> {-# OPTIONS_GHC -fno-warn-missing-signatures #-}

> module Language.Inch.Parser (parseModule, parseInterface) where

> import Control.Applicative
> import Control.Monad
> import Data.Char
> import Data.Maybe
> import Data.List

> import Text.ParserCombinators.Parsec hiding (parse, optional, many, (<|>))
> import Text.ParserCombinators.Parsec.Expr
> import Text.ParserCombinators.Parsec.Language
> import qualified Text.ParserCombinators.Parsec.Token as T
> import qualified Text.ParserCombinators.Parsec.IndentParser as I
> import qualified Text.ParserCombinators.Parsec.IndentParser.Token as IT


> import Language.Inch.Type
> import Language.Inch.Syntax
> import Language.Inch.Kit
> import Language.Inch.Kind hiding (kind)

> parseModule = I.parse module_

> parseInterface = I.parse interface

> def = haskellDef { identStart = identStart haskellDef <|> char '_' 
>                  , reservedNames = "_" : reservedNames haskellDef }

> lexer       = T.makeTokenParser def    
      
> identifier     = IT.identifier lexer
> reserved       = IT.reserved lexer
> operator       = IT.operator lexer
> reservedOp     = IT.reservedOp lexer
> charLiteral    = IT.charLiteral lexer
> stringLiteral  = IT.stringLiteral lexer
> natural        = IT.natural lexer
> integer        = IT.integer lexer
> symbol         = IT.symbol lexer
> whiteSpace     = IT.whiteSpace lexer
> parens         = IT.parens lexer
> braces         = IT.braces lexer
> brackets       = IT.brackets lexer
> dot            = IT.dot lexer
> commaSep       = IT.commaSep lexer
> commaSep1      = IT.commaSep1 lexer

< lexeme         = IT.lexeme lexer
< angles         = IT.angles lexer
< semi           = IT.semi lexer
< comma          = IT.comma lexer
< colon          = IT.colon lexer
< semiSep        = IT.semiSep lexer
< semiSep1       = IT.semiSep1 lexer

> backticks p = reservedOp "`" *> p <* reservedOp "`"

> specialOp s = try $
>     string s >> notFollowedBy (opLetter def) >> whiteSpace

> optionalList p = maybe [] id <$> optional p

> doubleColon = reservedOp "::"

> underscore = reserved "_"

> wrapParens p = (\ s -> "(" ++ s ++ ")") <$> p

> isVar :: String -> Bool
> isVar ('_':_:_)  = True
> isVar (x:_)      = isLower x
> isVar []         = error "isVar: empty"

> isVarOp :: String -> Bool
> isVarOp (':':_)  = False
> isVarOp _        = True

> identLike v desc = try $ do
>     s <- identifier <?> desc
>     when (v /= isVar s) $ fail $ "expected " ++ desc
>     return s

> opLike v desc = try $ do
>     s <- operator <?> desc
>     when (v /= isVarOp s) $ fail $ "expected " ++ desc
>     return s


> varid   = identLike True "variable"
> conid   = identLike False "constructor"
> varsym  = wrapParens (opLike True "variable symbol")
> consym  = wrapParens (opLike False "constructor symbol")

> var     = varid <|> try (parens varsym)
> con     = conid <|> try (parens consym)
> varop   = varsym <|> backticks varid
> conop   = consym <|> backticks conid

< op      = varop <|> conop

> gcon    =    reservedOp "()" *> return "()"
>         <|>  reservedOp "[]" *> return "[]"
>         <|>  reservedOp "(,)" *> return "(,)"
>         <|>  con




Kinds

> kind       = kindBit `chainr1` kindArrow
> kindBit    = setKind <|> try numKind <|> natKind <|> parens kind
> setKind    = symbol "*" >> return SKSet
> numKind    = (symbol "Integer" <|> symbol "Num") >> return SKNum
> natKind    = symbol "Nat" >> return SKNat
> kindArrow  = reservedOp "->" >> return (:-->)



Types

> tyVarName  = identLike True "type variable"
> tyConName  = identLike False "type constructor"
>              <|> try (reservedOp "()" >> return unitTypeName)
> numVarName = identLike True "numeric type variable"
> tyVar      = STyVar <$> tyVarName
> tyCon      = STyCon <$> tyConName
> tyExp      = tyAll <|> tyPi <|> tyQual <|> tyExpArr
> tyAll      = tyQuant "forall" (SBind All)
> tyPi       = tyQuant "pi" (SBind Pi)
> tyExpArr   = tyBit `chainr1` tyArrow
> tyArrow    = reservedOp "->" >> return (--->)

> tyBit = buildExpressionParser
>     [
>         [prefix "-" negate],
>         [binary "^" (sbinOp Pow) AssocLeft],
>         [binary "*" (*) AssocLeft],    
>         [binary "+" (+) AssocLeft, sbinary "-" (-) AssocLeft]
>     ]
>     (tyAtom `chainl1` pure STyApp)

> tyAtom     =    STyInt <$> try natural
>            <|>  SBinOp <$> prefixBinOp
>            <|>  SUnOp <$> prefixUnOp
>            <|>  tyVar
>            <|>  tyCon
>            <|>  parens ((reservedOp "->" *> pure SArr) <|> fmap (foldr1 (STyApp . STyApp (STyCon tupleTypeName))) (commaSep1 tyExp))
>            <|>  brackets (STyApp (STyCon listTypeName) <$> tyExp)

> prefixBinOp  =    reserved "min" *> pure Min
>              <|>  reserved "max" *> pure Max
>              <|>  try (parens ((specialOp "-" *> pure Minus)
>                                <|> (reservedOp "*" *> pure Times)
>                                <|> (reservedOp "+" *> pure Plus)
>                                <|> (reservedOp "^" *> pure Pow)))

> prefixUnOp   =    reserved "abs" *> pure Abs
>              <|>  reserved "signum" *> pure Signum

> prefixComparator  =    reservedOp "(==)" *> pure EL
>                   <|>  reservedOp "(>=)" *> pure GE
>                   <|>  reservedOp "(>)"  *> pure GR
>                   <|>  reservedOp "(<=)" *> pure LE
>                   <|>  reservedOp "(<)"  *> pure LS

> binary   name fun assoc = Infix (do{ reservedOp name; return fun }) assoc
> sbinary  name fun assoc = Infix (do{ specialOp name; return fun }) assoc
> prefix   name fun       = Prefix (do{ reservedOp name; return fun })

< postfix  name fun       = Postfix (do{ reservedOp name; return fun })


> tyQuant q f = do
>     reserved q
>     aks <- many1 $ foo <$> quantifiedVar
>     reservedOp "."
>     t <- tyExp
>     return $ foldr (\ (a, k) ty -> f a k ty) t $ join aks
>   where
>     foo :: ([as], k) -> [(as, k)]
>     foo (as, k) = map (\ a -> (a, k)) as

> quantifiedVar  =    parens ((,) <$> many1 tyVarName <* doubleColon <*> kind)
>                <|>  (\ a -> ([a] , SKSet)) <$> tyVarName

> tyQual = do
>     ps <- try (predicates <* reservedOp "=>")
>     t <- tyExp
>     return $ foldr SQual t ps

> predicates = commaSep1 predicate

> predicate = do
>     n   <- tyBit
>     op  <- predOp
>     m   <- tyBit
>     return $ op n m

> predOp = eqPred <|> lPred <|> lePred <|> gPred <|> gePred

> eqPred  = reservedOp  "~"   *> pure (%==%)
> lPred   = specialOp   "<"   *> pure (%<%)
> lePred  = specialOp   "<="  *> pure (%<=%)
> gPred   = specialOp   ">"   *> pure (%>%)
> gePred  = specialOp   ">="  *> pure (%>=%)





Terms

> expr = do
>     t    <- lexp
>     mty  <- optionMaybe (doubleColon >> tyExp)
>     case mty of
>         Just ty -> return $ t :? ty
>         Nothing -> return t

> lexp  =    lambda
>       <|>  letExpr
>       <|>  caseExpr
>       <|>  fexp


> letExpr = do
>     reserved "let"
>     ds <- I.block decls
>     reserved "in"
>     t <- expr
>     return $ Let ds t

> caseExpr = do
>     reserved "case"
>     t <- expr
>     reserved "of"
>     as <- I.block $ many caseAlternative
>     return $ Case t as

> caseAlternative = I.lineFold (CaseAlt <$> pat <*> altRest (reservedOp "->")
>     <?> "case alternative")

> fexp = buildExpressionParser
>     [
>         [prefix "-" (tmBinOp Minus (TmInt 0))],
>         [binary "^" (tmBinOp Pow) AssocLeft],
>         [binary "*" (tmBinOp Times) AssocLeft],    
>         [binary "+" (tmBinOp Plus) AssocLeft, sbinary "-" (tmBinOp Minus) AssocLeft],
>         [binary ":" (TmApp . TmApp (TmCon listConsName)) AssocRight]
>     ]
>     (aexp `chainl1` pure TmApp)

> aexp :: I.IndentCharParser st (STerm ())
> aexp  =    TmInt <$> try natural
>       <|>  CharLit <$> charLiteral
>       <|>  StrLit  <$> stringLiteral
>       <|>  TmBinOp <$> prefixBinOp
>       <|>  TmUnOp <$> prefixUnOp
>       <|>  TmComp <$> prefixComparator
>       <|>  TmVar <$> var
>       <|>  TmCon <$> gcon
>       <|>  parens (fmap (foldr1 (TmApp . TmApp (TmCon tupleConsName))) (commaSep1 expr))
>       <|>  braces (TmBrace <$> tyBit) 
>       <|>  listy

> listy = foldr (TmApp . TmApp (TmCon listConsName)) (TmCon listNilName) <$> brackets (commaSep fexp)

> lambda = do
>     reservedOp "\\"
>     ss <- many1 $ (Left <$> var) <|> (Right <$> braces numVarName)
>     reservedOp "->"
>     t <- expr
>     return $ wrapLam ss t
>   where
>     wrapLam []              t = t
>     wrapLam (Left s : ss)   t = Lam s $ wrapLam ss t
>     wrapLam (Right s : ss)  t = NumLam s $ rawCoerce $ wrapLam ss t


Interface files

> interface = many (dataDecl <|> sigDecl)


Modules

> module_ = do
>     whiteSpace
>     _ <- optional (reserved "#line" >> integer >> stringLiteral)
>     mh <- optional (reserved "module" *>
>                        ((,) <$> moduleName
>                            <*> optionalList (parens (commaSep identifier)))
>                     <* reserved "where")
>     is <- many importStmt
>     ds <- topdecls
>     eof
>     return $ Mod mh is ds

> importStmt = do
>     reserved "import"
>     q   <- isJust <$> optional (reserved "qualified")
>     n   <- moduleName
>     as  <- optional (reserved "as" *> moduleName)
>     im  <- importSpec
>     return $ Import q n as im

> importSpec =    Imp <$> parens (commaSep identifier)
>            <|>  ImpHiding <$> (reserved "hiding" *> parens (commaSep identifier))
>            <|>  pure ImpAll

> moduleName = join . intersperse "." <$> identLike False "module name" `sepBy` dot


> topdecls  = associate <$> many (dataDecl <|> sigDecl <|> funDecl)
> decls     = associate <$> many (sigDecl <|> funDecl)

> associate :: [SDeclaration ()] -> [SDeclaration ()]
> associate = map joinFun . groupBy sameFun
>   where
>     sameFun (FunDecl x _) (FunDecl y _)  = x == y
>     sameFun _             _              = False
> 
>     joinFun :: [SDeclaration ()] -> SDeclaration ()
>     joinFun [d] = d
>     joinFun fs@(FunDecl x _ : _) = FunDecl x (join (map altsOf fs))
>     joinFun _ = error "joinFun: impossible"

>     altsOf (FunDecl _ as) = as
>     altsOf _ = error "altsOf: impossible"

> dataDecl = I.lineFold $ do
>     try (reserved "data")
>     s <- tyConName
>     k <- (doubleColon >> kind) <|> return SKSet
>     reserved "where"
>     cs <- many $ I.lineFold constructor
>     ds <- maybe [] id <$> optional (reserved "deriving" >>
>               parens (commaSep className)
>               <|> fmap pure className)
>     return $ DataDecl s k cs ds
>     

> className = identLike False "type class name"

> constructor = do
>     s <- con
>     doubleColon
>     t <- tyExp
>     return $ s ::: t


> sigDecl = I.lineFold $ do
>     s   <- try $ var <* doubleColon
>     ty  <- tyExp
>     return $ SigDecl s ty


> funDecl = I.lineFold $ do
>     (v, ps)  <- funlhs
>     gt       <- rhs
>     return $ FunDecl v [Alt (foldr (:!) P0 ps) gt]


> altRest p  =    Unguarded <$> (p *> expr) <*> whereClause
>            <|>  Guarded <$> (many1 (reservedOp "|" *> ((:*:) <$> guarded <* p <*> expr)))
>                     <*> whereClause

> guarded  =    NumGuard <$> braces predicates
>          <|>  ExpGuard <$> commaSep expr

> whereClause = maybe [] id <$> optional (reserved "where" >> I.block decls)





> funlhs  =    (,) <$> var <*> many apat
>         <|>  (\ x o y -> (o, [x, y])) <$> pat <*> varop <*> pat
>         <|>  (\ (o, ps) qs -> (o, ps ++ qs)) <$> parens funlhs <*> many apat

> rhs = (Unguarded <$> (reservedOp "=" *> expr)
>     <|> Guarded <$> (many1 (reservedOp "|" *> ((:*:) <$> guarded <* reservedOp "=" <*> expr))))
>     <*> whereClause


> patList  =    (:!) <$> apat <*> patList
>          <|>  pure P0

> pat = do
>     l   <- lpat
>     mr  <- optional ((,) <$> conop <*> pat)
>     case mr of
>         Nothing      -> return l
>         Just (o, r)  -> return $ PatCon o (l :! r :! P0)

> lpat  =    PatCon <$> gcon <*> patList
>       <|>  apat

> apat =        nplusk
>          <|>  PatCon <$> gcon <*> pure P0
>          <|>  PatIntLit <$> try integer
>          <|>  underscore *> pure PatIgnore
>          <|>  parens (foldr1 tupleConsPat <$> commaSep1 pat)
>          <|>  brackets (foldr listConsPat listNilPat <$> commaSep pat)
>          <|>  braces patBrace
>   where
>     tupleConsPat x y  = PatCon tupleConsName (x :! y :! P0)
>     listConsPat x y   = PatCon listConsName (x :! y :! P0)
>     listNilPat        = PatCon listNilName P0

> nplusk = do
>     v <- var
>     mk <- optional (reservedOp "+" *> integer)
>     return $ case mk of
>        Nothing  -> PatVar v
>        Just k   -> PatNPlusK v k


> patBrace = do
>     ma  <- optional var
>     k   <- option 0 $ case ma of
>                           Just _   -> reservedOp "+" *> integer
>                           Nothing  -> integer
>     return $ case ma of
>         Just a   -> rawCoerce2 $ PatBrace a k
>         Nothing  -> PatBraceK k
