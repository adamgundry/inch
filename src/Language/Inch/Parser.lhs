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
> import Language.Inch.ModuleSyntax
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

> single p = (\ x -> [x]) <$> p
> manymany p = join <$> many p 

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

> gtycon =     reservedOp "()" *> return "()"
>         <|>  reservedOp "[]" *> return "[]"
>         <|>  reservedOp "(,)" *> return "(,)"
>         <|>  con



Kinds

> kind       = kindBit `chainr1` kindArrow
> kindBit    = setKind <|> try numKind <|> natKind <|> constraintKind <|> parens kind
> setKind    = symbol "*" >> return SKSet
> numKind    = (symbol "Integer" <|> symbol "Num") >> return SKNum
> natKind    = symbol "Nat" >> return SKNat
> constraintKind = symbol "Constraint" >> return SKConstraint
> kindArrow  = reservedOp "->" >> return (:-->)



Types

> tyVarName  = identLike True "type variable"
> tyConName  = identLike False "type constructor"
>              <|> try (reservedOp "()" >> return unitTypeName)
> numVarName = identLike True "numeric type variable"
> tyVar      = STyVar <$> tyVarName
> tyCon      = STyCon <$> gtycon
> tyExp      = tyAll <|> tyPi <|> tyQual <|> tyExpArr
> tyAll      = tyQuant "forall" (SBind All)
> tyPi       = tyQuant "pi" (SBind Pi)
> tyExpArr   = tyBit `chainr1` tyArrow
> tyArrow    = reservedOp "->" *> return (--->)
>            <|> reservedOp "=>" *> return SQual

> tyBit = buildExpressionParser
>     [  [prefix "-" negate]
>     ,  [binary "^" (sbinOp Pow) AssocLeft]
>     ,  [binary "*" (*) AssocLeft]
>     ,  [binary "+" (+) AssocLeft, sbinary "-" (-) AssocLeft]
>     ,  [  binary "<"  (styPred LS) AssocNone
>        ,  binary "<=" (styPred LE) AssocNone
>        ,  binary ">"  (styPred GR) AssocNone
>        ,  binary ">=" (styPred GE) AssocNone
>        ,  binary "~"  (styPred EL) AssocNone
>        ] 
>     ]
>     (tyAtom `chainl1` pure STyApp)

> tyAtom     =    STyInt <$> try natural
>            <|>  SBinOp <$> prefixBinOp
>            <|>  SUnOp <$> prefixUnOp
>            <|>  STyComp <$> prefixComparator
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

> prefixComparator  =    reservedOp "(~)" *> pure EL
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
>     ps <- try ((parens constraints <|> (pure <$> tyBit)) <* reservedOp "=>")
>     t <- tyExp
>     return $ foldr SQual t ps

> constraints = commaSep1 constraint
> constraint = tyBit

> predicates = commaSep1 predicate

> predicate = do
>     c <- constraint
>     case sConstraintToPred c of
>         Just p   -> return p
>         Nothing  -> fail "expected testable predicate"




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

> interface = manymany (   single dataDecl
>                      <|> single typeDecl
>                      <|> single classDecl
>                      <|> single instHeader
>                      <|> map Decl <$> sigDecls
>                      ) <* eof


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
>            <|>  ImpHiding <$> (reserved "hiding" *> parens (commaSep (var <|> con)))
>            <|>  pure ImpAll

> moduleName = join . intersperse "." <$> identLike False "module name" `sepBy` dot


> topdecls  = associateTop <$> manymany (   single dataDecl
>                                       <|> single typeDecl
>                                       <|> single classDecl
>                                       <|> single instDecl
>                                       <|> map Decl <$> (sigDecls <|> single funDecl)
>                                       )
>  where
>     associateTop :: [STopDeclaration] -> [STopDeclaration]
>     associateTop = map joinFun . groupBy sameFun
>
>     sameFun (Decl (FunDecl x _)) (Decl (FunDecl y _))  = x == y
>     sameFun _             _                            = False
> 
>     joinFun :: [STopDeclaration] -> STopDeclaration
>     joinFun [d] = d
>     joinFun fs@(Decl (FunDecl x _) : _) = Decl (FunDecl x (join (map altsOf fs)))
>     joinFun _ = error "joinFun: impossible"
>
>     altsOf (Decl (FunDecl _ as)) = as
>     altsOf _ = error "altsOf: impossible"

> decls     = associate <$> manymany (sigDecls <|> single funDecl)
>   where
>     associate :: [SDeclaration ()] -> [SDeclaration ()]
>     associate = map joinFun . groupBy sameFun
>
>     sameFun (FunDecl x _) (FunDecl y _)  = x == y
>     sameFun _             _              = False
> 
>     joinFun :: [SDeclaration ()] -> SDeclaration ()
>     joinFun [d] = d
>     joinFun fs@(FunDecl x _ : _) = FunDecl x (join (map altsOf fs))
>     joinFun _ = error "joinFun: impossible"
>
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


> typeDecl = I.lineFold $ do
>     reserved "type"
>     x <- tyConName
>     t <- tySyn
>     return $ TypeDecl x t
>   where
>     tySyn = SSynTy <$> (reservedOp "=" *> tyExp)
>           <|> SSynAll <$> tyVarName <*> pure SKSet <*> tySyn
>           <|> (do
>                 (x, k)  <- kindParens
>                 t       <- tySyn
>                 return $ SSynAll x k t
>               )


> kindParens = parens ((,) <$> tyVarName <* doubleColon <*> kind)


> className = identLike False "type class name"

> classDecl = I.lineFold $ do
>     reserved "class"
>     ss  <- optionalList $ parens (commaSep tyExp) <* reservedOp "=>"
>     s   <- className
>     vs  <- many classVar
>     ms  <- optionalList (reserved "where" *> manymany tmtypes)
>     return $ CDecl s (ClassDecl vs ss ms) 
>   where
>     classVar = ( ((\ v -> VK v SKSet) <$> var)
>              <|> parens (VK <$> var <*> (doubleColon *> kind)))

> instDecl = I.lineFold $ do
>     reserved "instance"
>     t <- tyExp
>     (cs, s, ts) <- implyBits t
>     zs <- optionalList (reserved "where" *> many funline)
>     return $ IDecl s (InstDecl ts cs zs)


> implyBits :: Monad m => SType -> m ([SType], String, [SType])
> implyBits (SQual q t) = do
>     let qs = uncomma q
>     (cs, s, ts) <- implyBits t
>     return (qs ++ cs, s, ts)
>   where
>     uncomma (STyCon c `STyApp` x `STyApp` y)
>         | c == tupleConsName = uncomma x ++ uncomma y
>     uncomma x = [x]
> implyBits (STyApp f t) = do
>     ([], s, ts) <- implyBits f
>     return ([], s, ts ++ [t])
> implyBits (STyCon c) = return ([], c, [])
> implyBits _ = fail "ook"



> instHeader = instDecl


> constructor = do
>     s <- con
>     doubleColon
>     t <- tyExp
>     return $ s ::: t


> tmtypes = I.lineFold $ do
>     ss  <- try $ commaSep var <* doubleColon
>     ty  <- tyExp
>     return $ map (\ s -> s ::: ty) ss

> sigDecls = map (\ (s ::: ty) -> SigDecl s ty) <$> tmtypes

> funline = I.lineFold $ do
>     (v, ps)  <- funlhs
>     gt       <- rhs
>     return (v, [Alt (foldr (:!) P0 ps) gt])

> funDecl = uncurry FunDecl <$> funline

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


> rtc p  =    (:!) <$> p <*> rtc p
>        <|>  pure P0

> patList = rtc apat

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
>          <|>  PatStrLit <$> stringLiteral
>          <|>  PatCharLit <$> charLiteral
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
