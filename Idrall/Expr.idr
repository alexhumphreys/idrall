public export
Name : Type
Name = String

public export
Namespace : Type
Namespace = List (Name, Integer)
%name Namespace ns1, ns2, ns3

public export
data U = CType | Sort | Kind

export
Eq U where
  (==) CType CType = True
  (==) Sort Sort = True
  (==) Kind Kind = True
  (==) _ _ = False

export
Show U where
  show CType = "CType"
  show Sort = "Sort"
  show Kind = "Kind"
-- expressions

mutual
  public export
  data ImportStatement
    = LocalFile String
    | EnvVar String

  public export
  data Import
    = Raw ImportStatement
    | Resolved (Expr Void)

  public export
  data Expr a
    -- x
    = EVar Name
    | EConst U
    | EPi Name (Expr a) (Expr a)
    -- | Lam x A b ~ λ(x : A) -> b
    | ELam Name (Expr a) (Expr a)
    -- | > App f a ~ f a
    | EApp (Expr a) (Expr a)
    -- | > Let x Nothing r e ~ let x = r in e
    --   > Let x (Just t) r e ~ let x : t = r in e
    | ELet Name (Maybe (Expr a)) (Expr a) (Expr a)
    -- | > Annot x t ~ x : t
    | EAnnot (Expr a) (Expr a)
    -- | > x === y
    | EEquivalent (Expr a) (Expr a)
    -- | > assert : e
    | EAssert (Expr a)
    -- | > Bool ~ Bool
    | EBool
    -- | > BoolLit b ~ b
    | EBoolLit Bool
    -- | > BoolAnd x y ~ x && y
    | EBoolAnd (Expr a) (Expr a)
    -- | > Natural ~ Natural
    | ENatural
    -- | > NaturalLit n ~ n
    | ENaturalLit Nat
    -- | > NaturalIsZero ~ Natural/isZero
    | ENaturalIsZero (Expr a)
    -- | > EList a ~ List a
    | EList (Expr a)
    -- | > EList (Some e) [e', ...] ~ [] : List a
    | EListLit (Maybe (Expr a)) (List (Expr a))
    -- | > x # y
    | EListAppend (Expr a) (Expr a)
    | EEmbed Import

export
Show ImportStatement where
  show (LocalFile x) = "(LocalFile " ++ x ++ ")"
  show (EnvVar x) = "(EnvVar " ++ x ++ ")"

mutual
  export
  Show Import where
    show (Raw x) = "(Raw" ++ show x ++ ")"
    show (Resolved x) = "(Resolved " ++ show x ++ ")"

  export
  Show (Expr a) where
    show (EVar x) = "(EVar " ++ show x ++ ")"
    show (EConst x) = "(EConst " ++ show x ++ ")"
    show (EPi x y z) = "(EPi " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (ELam x y z) = "(ELam " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (EApp x y) = "(EApp " ++ show x ++ " " ++ show y ++ ")"
    show (ELet x y z w) = "(ELet " ++ show x ++ " " ++ show y ++ " " ++ show z ++ " " ++ show w ++ ")"
    show (EAnnot x y) = "(EAnnot " ++ show x ++ " " ++ show y ++ ")"
    show (EEquivalent x y) = "(EEquivalent " ++ show x ++ " " ++ show y ++ ")"
    show (EAssert x) = "(EAssert " ++ show x ++ ")"
    show EBool = "EBool"
    show (EBoolLit False) = "(EBoolLit False)"
    show (EBoolLit True) = "(EBoolLit True)"
    show (EBoolAnd x y) = "(EBoolAnd " ++ show x ++ " " ++ show y ++ ")"
    show ENatural = "ENatural"
    show (ENaturalLit k) = "(ENaturalLit " ++ show k ++ ")"
    show (ENaturalIsZero x) = "(ENaturalIsZero " ++ show x ++ ")"
    show (EList x) = "(EList " ++ show x ++ ")"
    show (EListLit Nothing xs) = "(EListLit Nothing " ++ show xs ++ ")"
    show (EListLit (Just x) xs) = "(EListLit (Just " ++ show x ++ ") " ++ show xs ++ ")"
    show (EListAppend x y) = "(EListAppend " ++ show x ++ " " ++ show y ++ ")"
    show (EEmbed x) = "(EEmbed " ++ show x ++ ")"
