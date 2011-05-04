> module Parser where

> import Control.Applicative
> import Control.Monad
> import Data.Char

> import Text.ParserCombinators.Parsec hiding (optional, many, (<|>))
> import Text.ParserCombinators.Parsec.Expr
> import Text.ParserCombinators.Parsec.Language
> import qualified Text.ParserCombinators.Parsec.Token as T
> import qualified Text.ParserCombinators.Parsec.IndentParser as I
> import qualified Text.ParserCombinators.Parsec.IndentParser.Token as IT


> import TyNum
> import Type
> import Syntax
> import Kit
> import Kind


> parse = I.parse

> toyDef = haskellDef

> lexer       = T.makeTokenParser toyDef    
      
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
>     string s >> notFollowedBy (opLetter toyDef) >> whiteSpace


> doubleColon = reservedOp "::"



Kinds

> kind       = kindBit `chainr1` kindArrow
> kindBit    = setKind <|> natKind <|> parens kind
> setKind    = symbol "*" >> return SKSet
> natKind    = symbol "Num" >> return SKNum
> kindArrow  = reservedOp "->" >> return (:-->)



Types

> tyVarName  = identLike True "type variable"
> tyConName  = identLike False "type constructor"
> tyVar      = STyVar <$> tyVarName
> tyCon      = STyCon <$> tyConName
> tyExp      = tyAll <|> tyPi <|> tyQual <|> tyExpArr
> tyAll      = tyQuant "forall" (SBind All)
> tyPi       = tyQuant "pi" (SBind Pi)
> tyExpArr   = tyBit `chainr1` tyArrow
> tyArrow    = reservedOp "->" >> return (--->)
> tyBit      = tyBob `chainl1` pure STyApp
> tyBob      =    tyVar
>            <|>  tyCon
>            <|>  STyNum <$> try tyNumTerm
>            <|>  parens (reservedOp "->" *> pure SArr <|> tyExp)

> numVarName   = identLike True "numeric type variable"

> tyNum = buildExpressionParser
>     [
>         [binary "*" (:*:) AssocLeft],    
>         [binary "+" (:+:) AssocLeft, binary "-" (-) AssocLeft]
>     ]
>     tyNumTerm

> tyNumTerm  =    NumVar <$> numVarName
>            <|>  NumConst <$> try integer
>            <|>  Neg <$> (specialOp "-" *> tyNumTerm)
>            <|>  parens tyNum

> binary  name fun assoc = Infix (do{ reservedOp name; return fun }) assoc
> prefix  name fun       = Prefix (do{ reservedOp name; return fun })
> postfix name fun       = Postfix (do{ reservedOp name; return fun })


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
>     n   <- tyNum
>     op  <- predOp
>     m   <- tyNum
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
>          <|>  fexp
> expi i = expi (i+1) -- <|> lexpi i <|> rexpi i


> letExpr = do
>     reserved "let"
>     ds <- I.block $ many (sigDecl <|> funDecl)
>     reserved "in"
>     t <- expr
>     return $ Let ds t

> {-
> letExpr = do
>     reserved "let"
>     a <- tmVarName
>     reservedOp "="
>     w <- expr
>     reserved "in"
>     t <- expr
>     return $ Let [FunDecl a Nothing [Pat [] Trivial w]] t
> -}

<   Let <$> (reserved "let" *> many funDecl <* reserved "in") <*> expr


> fexp = foldl1 TmApp <$> many1 aexp

> aexp :: I.IndentCharParser st STerm
> aexp  =    TmVar <$> tmVarName
>       <|>  TmCon <$> dataConName
>       <|>  TmInt <$> integer
>       <|>  parens expr
>       <|>  braces (TmBrace <$> tyNum) 

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
>     ss <- many1 tmVarName
>     reservedOp "->"
>     t <- expr
>     return $ wrapLam ss t
>   where
>     wrapLam [] t      = t
>     wrapLam (s:ss) t  = Lam s $ wrapLam ss t


Programs

> program = do
>     whiteSpace
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
>     s   <- try $ tmVarName <* reservedOp "::"
>     ty  <- tyExp
>     return $ SigDecl s ty


> funDecl = do
>     (s, p)  <- patternStart
>     ps      <- many $ patternFor s
>     return $ FunDecl s (p:ps)


> patternStart = I.lineFold $ (,) <$> tmVarName <*> pattern

> patternFor s = I.lineFold $ do
>     try $ do  x <- tmVarName
>               unless (s == x) $ fail $ "expected pattern for " ++ show s
>     pattern

> pattern = Pat <$> many patTerm <*> patRest <*> expr

> patTerm  =    parens (PatCon <$> dataConName <*> many patTerm)
>          <|>  braces patBrace
>          <|>  PatCon <$> dataConName <*> pure []
>          <|>  PatVar <$> patVarName
>          <|>  reservedOp "_" *> pure PatIgnore
>          

> patVarName = identLike True "pattern variable"

> patBrace = do
>     ma  <- optional patVarName
>     mk  <- optional $ case ma of
>                           Just _   -> reservedOp "+" *> integer
>                           Nothing  -> integer
>     return $ PatBrace ma (maybe 0 id mk)

> patRest  =    reservedOp "=" *> pure Nothing
>          <|>  reservedOp "|" *> (Just <$> guarded) <* reservedOp "="

> guarded  =    NumGuard <$> braces predicates
>          <|>  ExpGuard <$> expr


> signature = I.lineFold $ do
>     s <- try $ tmVarName <* doubleColon
>     t <- tyExp
>     return (s, t)