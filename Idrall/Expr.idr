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
  -- | > x === y
  | EEquivalent Expr Expr
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
  show (EVar x) = "(EVar " ++ show x ++ ")"
  show (EConst x) = "(EConst " ++ show x ++ ")"
  show (EPi x y z) = "(EPi " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
  show (ELam x y z) = "(ELam " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
  show (EApp x y) = "(EApp " ++ show x ++ " " ++ show y ++ ")"
  show (ELet x y z w) = "(ELet " ++ show x ++ " " ++ show y ++ " " ++ show z ++ " " ++ show w ++ ")"
  show (EAnnot x y) = "(EAnnot " ++ show x ++ " " ++ show y ++ ")"
  show EBool = "EBool"
  show (EBoolLit False) = "(EBoolLit False)"
  show (EBoolLit True) = "(EBoolLit True)"
  show (EBoolAnd x y) = "(EBoolAnd " ++ show x ++ " " ++ show y ++ ")"
  show ENatural = "ENatural"
  show (ENaturalLit k) = "(ENaturalLit " ++ show k ++ ")"
  show (ENaturalIsZero x) = "(ENaturalIsZero " ++ show x ++ ")"
