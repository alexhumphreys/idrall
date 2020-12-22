module Idrall.Expr

import Idrall.Path

import public Data.SortedMap

public export
Name : Type
Name = String

public export
data FieldName = MkFieldName String

public export
Show FieldName where
  show (MkFieldName x) = "(MkFieldName " ++ show x ++ ")"

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
    = EConst U
    | EVar Name Int
    | ELam Name (Expr a) (Expr a)
    -- | > App f a ~ f a
    | EPi Name (Expr a) (Expr a)
    -- | Lam x A b ~ λ(x : A) -> b
    | EApp (Expr a) (Expr a)
    -- | > Let x Nothing r e ~ let x = r in e
    --   > Let x (Just t) r e ~ let x : t = r in e
    | ELet Name (Maybe (Expr a)) (Expr a) (Expr a)
    -- | > Annot x t ~ x : t
    | EAnnot (Expr a) (Expr a)
    -- | > Bool ~ Bool
    | EBool
    -- | > BoolLit b ~ b
    | EBoolLit Bool
    -- | > BoolAnd x y ~ x && y
    | EBoolAnd (Expr a) (Expr a)
    -- | > BoolOr  x y ~  x || y
    | EBoolOr  (Expr a) (Expr a)
    -- | > BoolEQ  x y ~  x == y
    | EBoolEQ  (Expr a) (Expr a)
    -- | > BoolNE  x y ~  x != y
    | EBoolNE  (Expr a) (Expr a)
    -- | > BoolIf x y z ~ if x then y else z
    | EBoolIf (Expr a) (Expr a) (Expr a)
    -- | > Natural ~ Natural
    | ENatural
    -- | > NaturalLit n ~ n
    | ENaturalLit Nat
    -- | > NaturalIsZero ~ Natural/isZero
    | ENaturalIsZero
        -- | > NaturalEven                              ~  Natural/even
    | ENaturalEven
    -- | > NaturalOdd                               ~  Natural/odd
    | ENaturalOdd
    -- | > NaturalToInteger                         ~  Natural/toInteger
    | ENaturalToInteger
    -- | > NaturalShow                               ~  Natural/show
    | ENaturalShow
     -- | > NaturalPlus x y                          ~  x + y
    | ENaturalPlus (Expr a) (Expr a)
    -- | > NaturalTimes x y                         ~  x * y
    | ENaturalTimes (Expr a) (Expr a)
    -- | > Integer ~ Integer
    | EInteger
    -- | > EIntegerLit i ~ i
    | EIntegerLit Integer
    -- | > IntegerShow ~  Integer/show
    | EIntegerShow
    -- | > EIntegerNegate ~ Integer/negate
    | EIntegerNegate
    -- | > Double ~ Double
    | EDouble
    -- | > DoubleLit n ~ n
    | EDoubleLit Double
    -- | > DoubleShow ~  Double/show
    | EDoubleShow
    -- | > EText ~ Text
    | EText
    -- | > ETextLit (Chunks [(t1, e1), (t2, e2)] t3) ~  "t1${e1}t2${e2}t3"
    | ETextLit (Chunks a)
    -- | > EList a ~ List a
    | EList
    -- | > EList (Some e) [e', ...] ~ [] : List a
    | EListLit (Maybe (Expr a)) (List (Expr a))
    -- | > x # y
    | EListAppend (Expr a) (Expr a)
    -- | > List/build
    | EListBuild
    -- | > List/fold
    | EListFold
    -- | > List/length
    | EListLength
    -- | > List/head
    | EListHead
    -- | > List/last
    | EListLast
    -- | > List/indexed
    | EListIndexed
    -- | > List/reverse
    | EListReverse
    -- | > EOptional ~ Optional
    | EOptional
    -- | > Some a
    | ESome (Expr a)
    -- | > None
    | ENone
    -- | > x === y
    | EEquivalent (Expr a) (Expr a)
    -- | > assert : e
    | EAssert (Expr a)
    -- | > ERecord (fromList ((MkFieldName "Foo"), EBool)) ~ { Foo : Bool }
    | ERecord (SortedMap FieldName (Expr a))
    -- | > ERecordLit (fromList ((MkFieldName "Foo"), EBool)) ~ { Foo = Bool }
    | ERecordLit (SortedMap FieldName (Expr a))
    -- | > EUnion (fromList ((MkFieldName "Foo"), Nothing)) ~ < Foo >
    -- | > EUnion (fromList ((MkFieldName "Foo"), Just EBool)) ~ < Foo : Bool >
    | EUnion (SortedMap FieldName (Maybe (Expr a)))
    -- | > x /\ y
    | ECombine (Expr a) (Expr a)
    -- | > x //\\ y
    | ECombineTypes (Expr a) (Expr a)
    -- | > Prefer x y ~  x ⫽ y
    | EPrefer (Expr a) (Expr a)
    -- | > Merge x y (Just t ) ~  merge x y : t
    --   > Merge x y  Nothing  ~  merge x y
    | EMerge (Expr a) (Expr a) (Maybe (Expr a))
    -- | > EField (EVar "x" 0) (MkFieldName "Foo") ~ x.Foo
    | EField (Expr a) FieldName
    -- | > Project e (Left xs) ~ e.{ xs }
    --   > Project e (Right t) ~ e.(t)
    | EProject (Expr a) (Either (List FieldName) (Expr a))
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

  export
  Show (Expr a) where
    show (EConst x) = "(EConst " ++ show x ++ ")"
    show (EVar x i) = "(EVar " ++ show x ++ " " ++ show i ++ ")"
    show (ELam x y z) = "(ELam " ++ x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (EPi x y z) = "(EPi " ++ x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (EApp x y) = "(EApp " ++ show x ++ " " ++ show y ++ ")"
    show (ELet x y z w) = "(ELet " ++ show x ++ " " ++ show y ++ " " ++ show z ++ " " ++ show w ++ ")"
    show (EAnnot x y) = "(EAnnot " ++ show x ++ " " ++ show y ++ ")"
    show EBool = "EBool"
    show (EBoolLit False) = "(EBoolLit False)"
    show (EBoolLit True) = "(EBoolLit True)"
    show (EBoolAnd x y) = "(EBoolAnd " ++ show x ++ " " ++ show y ++ ")"
    show (EBoolOr x y) = "(EBoolOr " ++ show x ++ " " ++ show y ++ ")"
    show (EBoolEQ x y) = "(EBoolEQ " ++ show x ++ " " ++ show y ++ ")"
    show (EBoolNE x y) = "(EBoolNE " ++ show x ++ " " ++ show y ++ ")"
    show (EBoolIf x y z) = "(EBoolIf " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show ENatural = "ENatural"
    show (ENaturalLit k) = "(ENaturalLit " ++ show k ++ ")"
    show ENaturalIsZero = "ENaturalIsZero"
    show ENaturalEven = "ENaturalEven"
    show ENaturalOdd = "ENaturalOdd"
    show ENaturalToInteger = "ENaturalToInteger"
    show ENaturalShow = "NaturalShow"
    show (ENaturalPlus x y) = "(ENaturalPlus " ++ show x ++ " " ++ show y ++ ")"
    show (ENaturalTimes x y) = "(ENaturalTimes " ++ show x ++ " " ++ show y ++ ")"
    show EInteger = "EInteger"
    show (EIntegerLit x) = "(EIntegerLit " ++ show x ++ ")"
    show EIntegerShow = "EIntegerShow"
    show EIntegerNegate = "EIntegerNegate"
    show EDouble = "EDouble"
    show (EDoubleLit k) = "(EDoubleLit " ++ show k ++ ")"
    show EDoubleShow = "EDoubleShow"
    show EText = "EText"
    show (ETextLit x) = "(ETextLit " ++ show x ++ ")"
    show EList = "EList"
    show (EListLit Nothing xs) = "(EListLit Nothing " ++ show xs ++ ")"
    show (EListLit (Just x) xs) = "(EListLit (Just " ++ show x ++ ") " ++ show xs ++ ")"
    show (EListAppend x y) = "(EListAppend " ++ show x ++ " " ++ show y ++ ")"
    show EListBuild = "EListBuild"
    show EListFold = "EListFold"
    show EListHead = "EListHead"
    show EListLength = "EListLength"
    show EListLast = "EListLast"
    show EListIndexed = "EListIndexed"
    show EListReverse = "EListReverse"
    show EOptional = "EOptional"
    show ENone = "ENone"
    show (ESome x) = "(ESome " ++ show x ++ ")"
    show (EEquivalent x y) = "(EEquivalent " ++ show x ++ " " ++ show y ++ ")"
    show (EAssert x) = "(EAssert " ++ show x ++ ")"
    show (ERecord x) = "(ERecord " ++ show x ++ ")"
    show (ERecordLit x) = "(ERecordLit " ++ show x ++ ")"
    show (EUnion x) = "(EUnion " ++ show x ++ ")"
    show (ECombine x y) = "(ECombine " ++ show x ++ " " ++ show y ++ ")"
    show (ECombineTypes x y) = "(ECombineTypes " ++ show x ++ " " ++ show y ++ ")"
    show (EPrefer x y) = "(EPrefer " ++ show x ++ " " ++ show y ++ ")"
    show (EMerge x y z) = "(EMerge " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (EField x y) = "(EField " ++ show x ++ " " ++ show y ++ ")"
    show (EProject x y) = "(EField " ++ show x ++ " " ++ show y ++ ")"
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
