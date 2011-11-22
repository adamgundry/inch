> {-# LANGUAGE StandaloneDeriving, TypeOperators, GADTs,
>              FlexibleInstances, MultiParamTypeClasses, TypeFamilies #-}

> module Language.Inch.ModuleSyntax where

> import Control.Applicative
> import Data.Traversable

> import Language.Inch.Kit
> import Language.Inch.Kind
> import Language.Inch.Type
> import Language.Inch.Syntax

> type Module            = Mod OK
> type ClassDeclaration  = ClassDecl OK
> type InstDeclaration   = InstDecl OK
> type TopDeclaration    = TopDecl OK

> type SModule            = Mod RAW
> type SClassDeclaration  = ClassDecl RAW
> type SInstDeclaration   = InstDecl RAW
> type STopDeclaration    = TopDecl RAW


> type family ExTy s
> type instance ExTy OK = Ex (Ty ())
> type instance ExTy RAW = SType



> data Mod s = Mod { modName :: Maybe (String, [String])
>                  , modImports :: [Import]
>                  , modDecls :: [TopDecl s]
>                  }

> deriving instance Show (Mod RAW)
> deriving instance Eq (Mod RAW)

> instance TravTypes Mod where
>     travTypes    g (Mod mh is ds) = Mod mh is <$> traverse (travTypes g) ds
>     fogTypes     g (Mod mh is ds) = Mod mh is (map (fogTypes g) ds)
>     renameTypes  g (Mod mh is ds) = Mod mh is (map (renameTypes g) ds)

> data Import = Import  {  qualified   :: Bool
>                       ,  importName  :: String
>                       ,  asName      :: Maybe String
>                       ,  impSpec     :: ImpSpec
>                       }
>   deriving (Eq, Show)

> data ImpSpec = ImpAll | Imp [String] | ImpHiding [String]
>   deriving (Eq, Show)



> type ClassMeths s   = [TmName ::: AType s KSet]
> type ClassMethods   = ClassMeths OK
> type SClassMethods  = ClassMeths RAW

> data ClassDecl s = ClassDecl {  classVars     :: [VarKind s ()]
>                              ,  superclasses  :: [AType s KConstraint]
>                              ,  classMethods  :: ClassMeths s
>                              }

> deriving instance Eq (ClassDecl RAW)
> deriving instance Show (ClassDecl RAW)                            
> deriving instance Show (ClassDecl OK)

> instance TravTypes ClassDecl where
>     travTypes g (ClassDecl vs ss ms) =
>         ClassDecl vs <$> traverse g ss <*> traverse (\ (y ::: t) -> (y :::) <$> g t) ms 
>     fogTypes g (ClassDecl vs ss ms) =
>         ClassDecl (map (fogTypes1 g) vs)
>                   (map (fogTy' g []) ss)
>                   (map (\ (y ::: t) -> (y ::: fogTy' g [] t)) ms)
>     renameTypes g (ClassDecl vks ss ms) = 
>         ClassDecl (map (renameTypes1 g) vks)
>                   (map (renameTy g) ss)
>                   (map (\ (y ::: t) -> y ::: renameTy g t) ms)


> classKind :: SClassDeclaration -> Ex Kind
> classKind (ClassDecl vs _ _) = varListKind vs
>   where
>     varListKind :: [VarKind RAW ()] -> Ex Kind
>     varListKind [] = Ex KConstraint
>     varListKind (VK _ k : ks) = case (kindKind k, varListKind ks) of
>                                    (Ex k', Ex l) -> Ex (k' :-> l)

> lookupMethodType :: TmName -> ClassMethods -> Maybe (Type KSet)
> lookupMethodType x xs = lookup x (map (\ (a ::: b) -> (a, b)) xs)


> data InstDecl s = InstDecl {  instTypes        :: [ExTy s]
>                            ,  instConstraints  :: [AType s KConstraint]
>                            ,  instMethods      :: [(TmName, [Alt s ()])]
>                            }
>                            

> deriving instance Eq (InstDecl RAW)
> deriving instance Show (InstDecl RAW)
> deriving instance Show (InstDecl OK)

> instance TravTypes InstDecl where
>     travTypes g (InstDecl ts cs zs) = InstDecl
>         <$> traverse (travEx g) ts
>         <*> traverse g cs
>         <*> traverse (\ (n, as) -> (,) n <$> traverse (travTypes1 g) as) zs
>     fogTypes g (InstDecl ts cs zs) = InstDecl
>         (map (unEx2 (fogTy' g [])) ts)
>         (map (fogTy' g []) cs)
>         (map (\ (n, as) -> (n, map (fogTypes1 g) as)) zs)
>     renameTypes g (InstDecl ts cs zs) = InstDecl
>         (map (mapEx (renameTy g)) ts)
>         (map (renameTy g) cs)
>         (map (\ (n, as) -> (n, map (renameTypes1 g) as)) zs)



> data TopDecl s where
>     DataDecl  :: TyConName -> AKind s k -> [TmConName ::: AType s KSet] ->
>                      [String] -> TopDecl s
>     CDecl     :: ClassName -> ClassDecl s -> TopDecl s
>     IDecl     :: ClassName -> InstDecl s -> TopDecl s 
>     Decl      :: Decl s () -> TopDecl s

> deriving instance Show (TopDecl RAW)
> deriving instance Show (TopDecl OK)
> deriving instance Eq (TopDecl RAW)

> instance TravTypes TopDecl where

>     travTypes g (DataDecl x k cs ds) =
>         DataDecl x k <$> traverse (\ (y ::: t) -> (y :::) <$> g t) cs <*> pure ds
>     travTypes g (CDecl x d) = CDecl x <$> travTypes g d
>     travTypes g (IDecl x d) = IDecl x <$> travTypes g d
>     travTypes g (Decl d) = Decl <$> travTypes1 g d

>     fogTypes g (DataDecl x k cs ds) = DataDecl x (fogKind k)
>         (map (\ (y ::: t) -> y ::: fogTy' g [] t) cs)
>         ds
>     fogTypes g (CDecl x d) = CDecl x (fogTypes g d)
>     fogTypes g (IDecl x d) = IDecl x (fogTypes g d)
>     fogTypes g (Decl d)  = Decl (fogTypes1 g d)

>     renameTypes g (DataDecl x k cs ds) = DataDecl x k
>         (map (\ (y ::: t) -> y ::: renameTy g t) cs)
>         ds
>     renameTypes g (CDecl x d) = CDecl x (renameTypes g d)
>     renameTypes g (IDecl x d) = IDecl x (renameTypes g d)
>     renameTypes g (Decl d)  = Decl (renameTypes1 g d)


> topDeclName :: TopDecl s -> String
> topDeclName (DataDecl x _ _ _)  = x
> topDeclName (CDecl x _)         = x
> topDeclName (IDecl x _)         = x
> topDeclName (Decl d)            = declName d
