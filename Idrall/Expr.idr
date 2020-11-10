import Idrall.Path

import public Data.SortedMap

public export
Name : Type
Name = String

public export
data FieldName = MkFieldName String

public export
Show FieldName where
  show (MkFieldName x) = "(MkFieldName " ++ x

public export
Eq FieldName where
  (==) (MkFieldName x) (MkFieldName y) = x == y

public export
Ord FieldName where
  compare (MkFieldName x) (MkFieldName y) = compare x y

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
    = LocalFile FilePath
    | EnvVar String

  public export
  data Import a
    = Raw a
    | Resolved (Expr Void)

  public export
  data Chunks a = MkChunks (List (String, Expr a)) String

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
    -- | > Integer ~ Integer
    | EInteger
    -- | > EIntegerLit i ~ i
    | EIntegerLit Integer
    -- | > Natural ~ Natural
    | EIntegerNegate (Expr a)
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
    -- | > List/Head A [a]
    | EListHead (Expr a) (Expr a)
    -- | > EText ~ Text
    | EText
    -- | > ETextLit (Chunks [(t1, e1), (t2, e2)] t3) ~  "t1${e1}t2${e2}t3"
    | ETextLit (Chunks a)
    -- | > EOptional a ~ Optional a
    | EOptional (Expr a)
    -- | > None a
    | ENone (Expr a)
    -- | > Some a
    | ESome (Expr a)
    -- | > ERecord (fromList ((MkFieldName "Foo"), EBool)) ~ { Foo : Bool }
    | ERecord (SortedMap FieldName (Expr a))
    -- | > ERecordLit (fromList ((MkFieldName "Foo"), EBool)) ~ { Foo = Bool }
    | ERecordLit (SortedMap FieldName (Expr a))
    -- | > EUnion (fromList ((MkFieldName "Foo"), Nothing)) ~ < Foo >
    -- | > EUnion (fromList ((MkFieldName "Foo"), Just EBool)) ~ < Foo : Bool >
    | EUnion (SortedMap FieldName (Maybe (Expr a)))
    -- | > EField (EVar "x") (MkFieldName "Foo") ~ x.Foo
    | EField (Expr a) FieldName
    | EEmbed (Import a)

export
Show ImportStatement where
  show (LocalFile x) = "(LocalFile " ++ show x ++ ")"
  show (EnvVar x) = "(EnvVar " ++ x ++ ")"

mutual
  export
  Show (Import a) where
    show (Raw x) = "(Raw)" -- TODO show x
    show (Resolved x) = "(Resolved " ++ show x ++ ")"

  covering -- TODO Maybe idris2 thinks this is total?
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
    show EInteger = "EInteger"
    show (EIntegerLit x) = "(EIntegerLit " ++ show x ++ ")"
    show (EIntegerNegate x) = "(EIntegerNegate " ++ show x ++ ")"
    show ENatural = "ENatural"
    show (ENaturalLit k) = "(ENaturalLit " ++ show k ++ ")"
    show (ENaturalIsZero x) = "(ENaturalIsZero " ++ show x ++ ")"
    show (EList x) = "(EList " ++ show x ++ ")"
    show (EListLit Nothing xs) = "(EListLit Nothing " ++ show xs ++ ")"
    show (EListLit (Just x) xs) = "(EListLit (Just " ++ show x ++ ") " ++ show xs ++ ")"
    show (EListAppend x y) = "(EListAppend " ++ show x ++ " " ++ show y ++ ")"
    show (EListHead x y) = "(EListHead " ++ show x ++ " " ++ show y ++ ")"
    show EText = "EText"
    show (ETextLit x) = "(ETextLit " ++ show x ++ ")"
    show (EOptional x) = "(EOptional " ++ show x ++ ")"
    show (ENone x) = "(ENone " ++ show x ++ ")"
    show (ESome x) = "(ESome " ++ show x ++ ")"
    show (ERecord x) = "(ERecord " ++ show x ++ ")"
    show (ERecordLit x) = "(ERecordLit " ++ show x ++ ")"
    show (EUnion x) = "(EUnion " ++ show x ++ ")"
    show (EField x y) = "(EField " ++ show x ++ " " ++ show y ++ ")"
    show (EEmbed x) = "(EEmbed " ++ show x ++ ")"

  public export
  Show (Chunks a) where
    show (MkChunks xs x) = "MkChunks " ++ (show xs) ++ " " ++ show x

  -- TODO add Traversible for Expr a

public export
Semigroup (Chunks a) where
  (<+>) (MkChunks xysL zL) (MkChunks [] zR) = MkChunks xysL (zL <+> zR)
  (<+>) (MkChunks xysL zL) (MkChunks ((x, y) :: xysR) zR) =
    MkChunks (xysL ++ (zL <+> x, y)::xysR) zR

public export
Monoid (Chunks a) where
  neutral = MkChunks [] neutral
