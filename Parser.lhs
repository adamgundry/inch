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
> tyExp      = tyAll <|> tyPi <|> tyExpArr
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
> tyNum        = tyNumTerm `chainr1` tyPlusMinus
> tyPlusMinus  =    reservedOp "+" *> return (+)
>              <|>  specialOp "-" *> return (-)
>              <|>  reservedOp "*" *> return (*)
> tyNumTerm    =    NumVar <$> numVarName
>              <|>  NumConst <$> try integer
>              <|>  Neg <$> (specialOp "-" *> tyNumTerm)
>              <|>  parens tyNum
> 

> tyQuant q f = do
>     reserved q
>     aks <- many1 $ foo <$> quantifiedVar
>     reservedOp "."
>     mps <- optional $ try predicates
>     t <- tyExp
>     let t' = case mps of
>                  Just ps  -> foldr Qual t ps
>                  Nothing  -> t
>     return $ foldr (\ (a, k) t -> f a k (bind a t)) t' $ join aks
>   where
>     foo :: ([as], k) -> [(as, k)]
>     foo (as, k) = map (\ a -> (a, k)) as

> quantifiedVar  =    parens ((,) <$> many1 tyVarName <* doubleColon <*> kind)
>                <|>  (\ a -> ([a] , Set)) <$> tyVarName


> predicates = (predicate `sepBy1` reservedOp ",") <* reservedOp "=>"

> predicate = do
>     n   <- tyNumTerm
>     op  <- lePred <|> eqPred
>     m   <- tyNumTerm
>     return $ op n m

> lePred = reservedOp "<=" *> pure (:<=:)
> eqPred = reservedOp "~" *> pure (:==:)



Terms

> expr  =    lambda
>       <|>  fexp 

> fexp = do
>     t <- foldl1 TmApp <$> many1 aexp
>     mty <- optionMaybe (doubleColon >> tyExp)
>     case mty of
>         Just ty -> return $ t :? ty
>         Nothing -> return t

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
>     t <- fexp
>     return $ wrapLam ss t

> wrapLam [] t = t
> wrapLam (s:ss) t = lam s $ wrapLam ss t

> lam s = Lam s . bind s


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