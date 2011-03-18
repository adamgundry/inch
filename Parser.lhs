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
> import Orphans
> import Kit


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
> setKind    = symbol "*" >> return Set
> natKind    = symbol "Num" >> return KindNum
> kindArrow  = reservedOp "->" >> return KindArr



Types

> tyVarName  = identLike True "type variable"
> tyConName  = identLike False "type constructor"
> tyVar      = TyVar () <$> tyVarName
> tyCon      = mkTyCon <$> tyConName
> tyExp      = tyAll <|> tyPi <|> tyQual <|> tyExpArr
> tyAll      = tyQuant "forall" (Bind All)
> tyPi       = tyQuant "pi" (Bind Pi)
> tyExpArr   = tyBit `chainr1` tyArrow
> tyArrow    = reservedOp "->" >> return (-->)
> tyBit      = tyBob `chainl1` pure TyApp
> tyBob      =    tyVar
>            <|>  tyCon
>            <|>  TyNum <$> try tyNumTerm
>            <|>  parens (reservedOp "->" *> pure (TyB Arr) <|> tyExp)

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
>     return $ foldr (\ (a, k) ty -> f a k (bind a ty)) t $ join aks
>   where
>     foo :: ([as], k) -> [(as, k)]
>     foo (as, k) = map (\ a -> (a, k)) as

> quantifiedVar  =    parens ((,) <$> many1 tyVarName <* doubleColon <*> kind)
>                <|>  (\ a -> ([a] , Set)) <$> tyVarName

> tyQual = do
>     ps <- try predicates
>     t <- tyExp
>     return $ foldr Qual t ps

> predicates = (predicate `sepBy1` reservedOp ",") <* reservedOp "=>"

> predicate = do
>     n   <- tyNum
>     op  <- predOp
>     m   <- tyNum
>     return $ op n m

> predOp = eqPred <|> lPred <|> lePred <|> gPred <|> gePred

> eqPred  = reservedOp  "~"   *> pure (:==:)
> lPred   = specialOp   "<"   *> pure (\ m n -> (m :+: 1) :<=: n)
> lePred  = specialOp   "<="  *> pure (:<=:)
> gPred   = specialOp   ">"   *> pure (\ m n -> (n :+: 1) :<=: m)
> gePred  = specialOp   ">="  *> pure (flip (:<=:))





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
>     ds <- I.block $ many funDecl
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
>     wrapLam (s:ss) t  = lam s $ wrapLam ss t
>
>     lam s = Lam s . bind s


Programs

> program = do
>     whiteSpace
>     mn <- optional (reserved "module" *>
>                        identLike False "module name" <* reserved "where")
>     ds <- many decl
>     eof
>     return (ds, mn)

> decl  =    DD <$> dataDecl
>       <|>  FD <$> funDecl


> dataDecl = I.lineFold $ do
>     try (reserved "data")
>     s <- tyConName
>     k <- (doubleColon >> kind) <|> return Set
>     reserved "where"
>     cs <- many $ I.lineFold constructor
>     return $ DataDecl s k cs
>     



> constructor = do
>     s <- dataConName
>     doubleColon
>     t <- tyExp
>     return (s ::: t)



> funDecl = do
>     mst <- optional signature
>     case mst of
>         Just (s, t) -> FunDecl s (Just t) <$> many (patternFor s)
>         Nothing -> do
>             (s, p) <- patternStart
>             ps <- many $ patternFor s
>             return $ FunDecl s Nothing (p:ps)


> patternStart = I.lineFold $ (,) <$> tmVarName <*> pattern

> patternFor s = I.lineFold $ do
>     try $ do  x <- tmVarName
>               unless (s == x) $ fail $ "expected pattern for " ++ show s
>     pattern

> pattern = Pat <$> many patTerm <* reservedOp "=" <*> pure Trivial <*> expr

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

> signature = I.lineFold $ do
>     s <- try $ tmVarName <* doubleColon
>     t <- tyExp
>     return (s, t)