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
  show CType = "Type"
  show Sort = "Sort"
  show Kind = "Kind"
-- expressions

public export
data Expr
  -- x
  = EVar Name
  | EConst U
  | EPi Name Expr Expr
  -- | Lam x A b ~ λ(x : A) -> b
  | ELam Name Expr Expr
  -- | > App f a ~ f a
  | EApp Expr Expr
  -- | > Let x Nothing r e ~ let x = r in e
  --   > Let x (Just t) r e ~ let x : t = r in e
  | ELet Name (Maybe Expr) Expr Expr
  -- | > Annot x t ~ x : t
  | EAnnot Expr Expr
  -- | > Bool ~ Bool
  | EBool
  -- | > BoolLit b ~ b
  | EBoolLit Bool
  -- | > BoolAnd x y ~ x && y
  | EBoolAnd Expr Expr
  -- | > Natural ~ Natural
  | ENatural
  -- | > NaturalLit n ~ n
  | ENaturalLit Nat
  -- | > NaturalIsZero ~ Natural/isZero
  | ENaturalIsZero Expr

export
Show Expr where
  show (EVar x) = x
  show (EConst x) = show x
  show (EPi x y z) = ?foo_3
  show (ELam x y z) = ?foo_4
  show (EApp x y) = ?foo_5
  show (ELet x y z w) = ?foo_6
  show (EAnnot x y) = ?foo_7
  show EBool = "Bool"
  show (EBoolLit False) = "False"
  show (EBoolLit True) = "True"
  show (EBoolAnd x y) = ?foo_10
  show ENatural = "Natural"
  show (ENaturalLit k) = show k
  show (ENaturalIsZero x) = ?foo_13
