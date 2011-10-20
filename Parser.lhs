> module Parser (parseProgram) where

> import Control.Applicative
> import Control.Monad
> import Data.Char

> import Text.ParserCombinators.Parsec hiding (parse, optional, many, (<|>))
> import Text.ParserCombinators.Parsec.Expr
> import Text.ParserCombinators.Parsec.Language
> import qualified Text.ParserCombinators.Parsec.Token as T
> import qualified Text.ParserCombinators.Parsec.IndentParser as I
> import qualified Text.ParserCombinators.Parsec.IndentParser.Token as IT


> import Type
> import Syntax
> import Kit
> import Kind hiding (kind)

> parseProgram = I.parse program

> def = haskellDef

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
> lexeme         = IT.lexeme lexer
> whiteSpace     = IT.whiteSpace lexer
> parens         = IT.parens lexer
> braces         = IT.braces lexer
> angles         = IT.angles lexer
> brackets       = IT.brackets lexer
> semi           = IT.semi lexer
> comma          = IT.comma lexer
> colon          = IT.colon lexer
> dot            = IT.dot lexer
> semiSep        = IT.semiSep lexer
> semiSep1       = IT.semiSep1 lexer
> commaSep       = IT.commaSep lexer
> commaSep1      = IT.commaSep1 lexer


> specialOp s = try $
>     string s >> notFollowedBy (opLetter def) >> whiteSpace


> doubleColon = reservedOp "::"


Kinds

> kind       = kindBit `chainr1` kindArrow
> kindBit    = setKind <|> try numKind <|> natKind <|> parens kind
> setKind    = symbol "*" >> return SKSet
> numKind    = symbol "Num" >> return SKNum
> natKind    = symbol "Nat" >> return SKNat
> kindArrow  = reservedOp "->" >> return (:-->)



Types

> tyVarName  = identLike True "type variable"
> tyConName  = identLike False "type constructor"
> numVarName = identLike True "numeric type variable"
> tyVar      = STyVar <$> tyVarName
> numVar     = STyVar <$> numVarName
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
>            <|>  parens ((reservedOp "->" *> pure SArr) <|> tyExp)

> prefixBinOp  =    reserved "min" *> pure Min
>              <|>  reserved "max" *> pure Max
>              <|>  try (parens ((specialOp "-" *> pure Minus)
>                                <|> (reservedOp "*" *> pure Times)
>                                <|> (reservedOp "+" *> pure Plus)
>                                <|> (reservedOp "^" *> pure Pow)))

> prefixUnOp   =    reserved "abs" *> pure Abs
>              <|>  reserved "signum" *> pure Signum

> binary   name fun assoc = Infix (do{ reservedOp name; return fun }) assoc
> sbinary  name fun assoc = Infix (do{ specialOp name; return fun }) assoc
> prefix   name fun       = Prefix (do{ reservedOp name; return fun })
> postfix  name fun       = Postfix (do{ reservedOp name; return fun })


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

> predicates = predicate `sepBy1` reservedOp ","

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
>     t    <- expi 0
>     mty  <- optionMaybe (doubleColon >> tyExp)
>     case mty of
>         Just ty -> return $ t :? ty
>         Nothing -> return t

> expi 10  =    lambda
>          <|>  letExpr
>          <|>  caseExpr
>          <|>  fexp
> expi i = expi (i+1) -- <|> lexpi i <|> rexpi i


> letExpr = do
>     reserved "let"
>     ds <- I.block $ many (sigDecl <|> funDecl)
>     reserved "in"
>     t <- expr
>     return $ Let ds t

> caseExpr = do
>     reserved "case"
>     t <- expr
>     reserved "of"
>     as <- I.block $ many caseAlternative
>     return $ Case t as

> caseAlternative = I.lineFold (CaseAlt <$> casePattern <*> altRest (reservedOp "->")
>     <?> "case alternative")

> casePattern  =    PatCon <$> dataConName <*> patList
>              <|>  parens casePattern
>              <|>  PatVar <$> patVarName
>              <|>  reservedOp "_" *> pure PatIgnore

> fexp = pexp `chainl1` pure TmApp

> pexp = buildExpressionParser
>     [
>         [prefix "-" (tmBinOp Minus (TmInt 0))],
>         [binary "^" (tmBinOp Pow) AssocLeft],
>         [binary "*" (tmBinOp Times) AssocLeft],    
>         [binary "+" (tmBinOp Plus) AssocLeft, sbinary "-" (tmBinOp Minus) AssocLeft]
>     ]
>     aexp

> aexp :: I.IndentCharParser st (STerm ())
> aexp  =    TmVar <$> tmVarName
>       <|>  TmCon <$> dataConName
>       <|>  TmInt <$> try integer
>       <|>  parens expr
>       <|>  braces (TmBrace <$> tyBit) 

> isVar :: String -> Bool
> isVar = isLower . head

> identLike var desc = try $ do
>     s <- identifier <?> desc
>     when (var /= isVar s) $ fail $ "expected " ++ desc
>     return s

> tmVarName    = identLike True   "term variable"
> dataConName  = identLike False  "data constructor"

> lambda = do
>     reservedOp "\\"
>     ss <- many1 $ (Left <$> tmVarName) <|> (Right <$> braces numVarName)
>     reservedOp "->"
>     t <- expr
>     return $ wrapLam ss t
>   where
>     wrapLam []              t = t
>     wrapLam (Left s : ss)   t = Lam s $ wrapLam ss t
>     wrapLam (Right s : ss)  t = NumLam s $ rawCoerce $ wrapLam ss t


Programs

> program = do
>     whiteSpace
>     optional (reserved "#line" >> integer >> stringLiteral)
>     mn <- optional (reserved "module" *>
>                        identLike False "module name" <* reserved "where")
>     ds <- many decl
>     eof
>     return (ds, mn)

> decl  =    dataDecl
>       <|>  sigDecl
>       <|>  funDecl


> dataDecl = I.lineFold $ do
>     try (reserved "data")
>     s <- tyConName
>     k <- (doubleColon >> kind) <|> return SKSet
>     reserved "where"
>     cs <- many $ I.lineFold constructor
>     return $ DataDecl s k cs
>     



> constructor = do
>     s <- dataConName
>     doubleColon
>     t <- tyExp
>     return $ s ::: t


> sigDecl = I.lineFold $ do
>     s   <- try $ tmVarName <* doubleColon
>     ty  <- tyExp
>     return $ SigDecl s ty


> funDecl = do
>     (s, p)  <- alternativeStart
>     ps      <- many $ alternativeFor s
>     return $ FunDecl s (p:ps)


> alternativeStart = I.lineFold $ (,) <$> tmVarName <*> alternative

> alternativeFor s = I.lineFold $ try $ do
>     x <- tmVarName
>     unless (s == x) $ fail $ "expected pattern for " ++ show s
>     alternative

> alternative = Alt <$> patList <*> altRest (reservedOp "=")

> altRest p  =    Unguarded <$> (p *> expr)
>            <|>  Guarded <$> (many1 (reservedOp "|" *> ((:*:) <$> guarded <* p <*> expr)))

> guarded  =    NumGuard <$> braces predicates
>          <|>  ExpGuard <$> expr


> patList  =    (:!) <$> pattern <*> patList
>          <|>  pure P0

> pattern  =    parens (PatCon <$> dataConName <*> patList)
>          <|>  braces patBrace
>          <|>  PatCon <$> dataConName <*> pure P0
>          <|>  PatVar <$> patVarName
>          <|>  reservedOp "_" *> pure PatIgnore
>          

> patVarName = identLike True "pattern variable"

> patBrace = do
>     ma  <- optional patVarName
>     k   <- option 0 $ case ma of
>                           Just _   -> reservedOp "+" *> integer
>                           Nothing  -> integer
>     return $ case ma of
>         Just a   -> rawCoerce2 $ PatBrace a k
>         Nothing  -> PatBraceK k


> signature = I.lineFold $ do
>     s <- try $ tmVarName <* doubleColon
>     t <- tyExp
>     return (s, t)