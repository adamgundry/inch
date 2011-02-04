> {-# LANGUAGE GADTs #-}

> module Syntax where

> data Kind where
>     Set      :: Kind
>     NatKind  :: Kind
>     (::->)   :: Kind -> Kind -> Kind
>   deriving (Eq, Show)
> infixr 5 ::->

> data Ty a where
>     TyVar    :: a -> Ty a
>     TyCon    :: a -> Ty a
>     (:->)    :: Ty a -> Ty a -> Ty a
>     Pi       :: a -> Kind -> Ty a -> Ty a
>     All      :: a -> Kind -> Ty a -> Ty a
>   deriving (Eq, Show)
> infixr 5 :->

> data Tm a where
>     TmVar  :: a -> Tm a
>     TmCon  :: a -> Tm a
>     Lam    :: a -> Tm a -> Tm a 
>     (:$)   :: Tm a -> Tm a -> Tm a
>     (:?)   :: Tm a -> Ty a -> Tm a
>   deriving (Eq, Show)



> data Decl a where
>     DataDecl  :: a -> Kind -> [Con a] -> Decl a
>     FunDecl   :: a -> Maybe (Ty a) -> [Pat a] -> Decl a
>   deriving (Eq, Show)

> data Con a where
>     Con :: a -> Ty a -> Con a
>   deriving (Eq, Show)

> data Pat a where
>     Pat :: [PatTerm a] -> Guard a -> Tm a -> Pat a
>   deriving (Eq, Show)

> data PatTerm a where
>     PatVar :: a -> PatTerm a
>     PatCon :: a -> [PatTerm a] -> PatTerm a
>   deriving (Eq, Show)

> data Guard a where
>     Trivial :: Guard a
>   deriving (Eq, Show)


> type Term         = Tm String
> type Type         = Ty String
> type Pattern      = Pat String
> type Declaration  = Decl String
> type Program      = [Declaration]


> patToTm :: PatTerm a -> Tm a
> patToTm (PatVar a)     = TmVar a
> patToTm (PatCon a ps)  = foldl1 (:$) (TmCon a : map patToTm ps)