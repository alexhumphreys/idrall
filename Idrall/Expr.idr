module Idrall.Expr

import Data.List1

import Idrall.Path
import public Idrall.FC

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
prettyFieldName : FieldName -> String
prettyFieldName (MkFieldName x) = x

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
    | Http String
    | Missing

  public export
  data Import a
    = Raw a
    | Text a
    | Location a
    | Resolved (Expr Void)

  public export
  data Chunks a = MkChunks (List (String, Expr a)) String

  public export
  data Expr a
    -- x
    = EConst FC U
    | EVar FC Name Int
    -- | ELam x A b ~ λ(x : A) -> b
    | ELam FC Name (Expr a) (Expr a)
    -- | EPi x A b ~ forall(x : A) -> b
    | EPi FC Name (Expr a) (Expr a)
    -- | > EApp f a ~ f a
    | EApp FC (Expr a) (Expr a)
    -- | > ELet x Nothing r e ~ let x = r in e
    --   > ELet x (Just t) r e ~ let x : t = r in e
    | ELet FC Name (Maybe (Expr a)) (Expr a) (Expr a)
    -- | > EAnnot x t ~ x : t
    | EAnnot FC (Expr a) (Expr a)
    -- | > EBool ~ Bool
    | EBool FC
    -- | > EBoolLit b ~ b
    | EBoolLit FC Bool
    -- | > EBoolAnd x y ~ x && y
    | EBoolAnd FC (Expr a) (Expr a)
    -- | > EBoolOr  x y ~  x || y
    | EBoolOr FC (Expr a) (Expr a)
    -- | > EBoolEQ  x y ~  x == y
    | EBoolEQ FC (Expr a) (Expr a)
    -- | > EBoolNE  x y ~  x != y
    | EBoolNE FC (Expr a) (Expr a)
    -- | > EBoolIf x y z ~ if x then y else z
    | EBoolIf FC (Expr a) (Expr a) (Expr a)
    -- | > ENatural ~ Natural
    | ENatural FC
    -- | > ENaturalLit n ~ n
    | ENaturalLit FC Nat
    -- | > ENaturalFold ~ Natural/fold
    | ENaturalFold FC
    -- | > ENaturalBuild ~ Natural/build
    | ENaturalBuild FC
    -- | > ENaturalIsZero ~ Natural/isZero
    | ENaturalIsZero FC
    -- | > ENaturalEven ~  Natural/even
    | ENaturalEven FC
    -- | > ENaturalOdd ~  Natural/odd
    | ENaturalOdd FC
    -- | > ENaturalToInteger ~  Natural/toInteger
    | ENaturalToInteger FC
    -- | > ENaturalSubtract ~  Natural/subtract
    | ENaturalSubtract FC
    -- | > ENaturalShow ~  Natural/show
    | ENaturalShow FC
     -- | > ENaturalPlus x y ~  x + y
    | ENaturalPlus FC (Expr a) (Expr a)
    -- | > ENaturalTimes x y ~  x * y
    | ENaturalTimes FC (Expr a) (Expr a)
    -- | > EInteger ~ Integer
    | EInteger FC
    -- | > EIntegerLit i ~ i
    | EIntegerLit FC Integer
    -- | > EIntegerShow ~  Integer/show
    | EIntegerShow FC
    -- | > EIntegerClamp ~ Integer/clamp
    | EIntegerClamp FC
    -- | > EIntegerNegate ~ EIntegerNegate
    | EIntegerNegate FC
    -- | > EIntegerToDouble ~ EIntegerToDouble
    | EIntegerToDouble FC
    -- | > EDouble ~ Double
    | EDouble FC
    -- | > EDoubleLit n ~ n
    | EDoubleLit FC Double
    -- | > EDoubleShow ~  Double/show
    | EDoubleShow FC
    -- | > EText ~ Text
    | EText FC
    -- | > ETextLit (Chunks [(t1, e1), (t2, e2)] t3) ~  "t1${e1}t2${e2}t3"
    | ETextLit FC (Chunks a)
    -- | > ETextAppend x y ~ x ++ y
    | ETextAppend FC (Expr a) (Expr a)
    -- | > ETextShow ~ Text/show
    | ETextShow FC
    -- | > ETextReplace ~ Text/replace
    | ETextReplace FC
    -- | > EList a ~ List a
    | EList FC
    -- | > EList (Some e) [e', ...] ~ [] : List a
    | EListLit FC (Maybe (Expr a)) (List (Expr a))
    -- | > EListAppend x y ~ x # y
    | EListAppend FC (Expr a) (Expr a)
    -- | > EListBuild ~ List/build
    | EListBuild FC
    -- | > EListFold ~ List/fold
    | EListFold FC
    -- | > EListLength ~ List/length
    | EListLength FC
    -- | > EListHead ~ List/head
    | EListHead FC
    -- | > EListLast ~ List/last
    | EListLast FC
    -- | > EListIndexed ~ List/indexed
    | EListIndexed FC
    -- | > EListReverse ~ List/reverse
    | EListReverse FC
    -- | > EOptional ~ Optional
    | EOptional FC
    -- | > ESome x ~ Some a
    | ESome FC (Expr a)
    -- | > ENone ~ None
    | ENone FC
    -- | > EEquivalent x y ~ x === y
    | EEquivalent FC (Expr a) (Expr a)
    -- | > EAssert x ~ assert : e
    | EAssert FC (Expr a)
    -- | > ERecord (fromList ((MkFieldName "Foo"), EBool)) ~ { Foo : Bool }
    | ERecord FC (SortedMap FieldName (Expr a))
    -- | > ERecordLit (fromList ((MkFieldName "Foo"), EBool)) ~ { Foo = Bool }
    | ERecordLit FC (SortedMap FieldName (Expr a))
    -- | > EUnion (fromList ((MkFieldName "Foo"), Nothing)) ~ < Foo >
    -- | > EUnion (fromList ((MkFieldName "Foo"), Just EBool)) ~ < Foo : Bool >
    | EUnion FC (SortedMap FieldName (Maybe (Expr a)))
    -- | > ECombine x y ~ x /\ y
    | ECombine FC (Expr a) (Expr a)
    -- | > ECombineTypes x y ~ x //\\ y
    | ECombineTypes FC (Expr a) (Expr a)
    -- | > EPrefer x y ~  x ⫽ y
    | EPrefer FC (Expr a) (Expr a)
    -- | > ERecordCompletion x y ~  x::y
    | ERecordCompletion FC (Expr a) (Expr a)
    -- | > EMerge x y (Just t ) ~  merge x y : t
    --   > EMerge x y  Nothing  ~  merge x y
    | EMerge FC (Expr a) (Expr a) (Maybe (Expr a))
    -- | > EToMap x (Just t) ~  toMap x : t
    --   > EToMap x Nothing ~  toMap x
    | EToMap FC (Expr a) (Maybe (Expr a))
    -- | > EField (EVar "x" 0) (MkFieldName "Foo") ~ x.Foo
    | EField FC (Expr a) FieldName
    -- | > EProject e (Left xs) ~ e.{ xs }
    --   > EProject e (Right t) ~ e.(t)
    | EProject FC (Expr a) (Either (List FieldName) (Expr a))
    -- | > EWith x y e ~  x with y = e
    | EWith FC (Expr a) (List1 FieldName) (Expr a)
    -- | > EImportAlt x y ~ x ? y
    | EImportAlt FC (Expr a) (Expr a)
    | EEmbed FC (Import a)

public export
HasFC (Expr a) where
  getFC (EConst fc x) = fc
  getFC (EVar fc x y) = fc
  getFC (ELam fc x y z) = fc
  getFC (EPi fc x y z) = fc
  getFC (EApp fc x y) = fc
  getFC (ELet fc x y z w) = fc
  getFC (EAnnot fc x y) = fc
  getFC (EBool fc) = fc
  getFC (EBoolLit fc x) = fc
  getFC (EBoolAnd fc x y) = fc
  getFC (EBoolOr fc x y) = fc
  getFC (EBoolEQ fc x y) = fc
  getFC (EBoolNE fc x y) = fc
  getFC (EBoolIf fc x y z) = fc
  getFC (ENatural fc) = fc
  getFC (ENaturalLit fc k) = fc
  getFC (ENaturalFold fc) = fc
  getFC (ENaturalBuild fc) = fc
  getFC (ENaturalIsZero fc) = fc
  getFC (ENaturalEven fc) = fc
  getFC (ENaturalOdd fc) = fc
  getFC (ENaturalToInteger fc) = fc
  getFC (ENaturalSubtract fc) = fc
  getFC (ENaturalShow fc) = fc
  getFC (ENaturalPlus fc x y) = fc
  getFC (ENaturalTimes fc x y) = fc
  getFC (EInteger fc) = fc
  getFC (EIntegerLit fc x) = fc
  getFC (EIntegerShow fc) = fc
  getFC (EIntegerClamp fc) = fc
  getFC (EIntegerNegate fc) = fc
  getFC (EIntegerToDouble fc) = fc
  getFC (EDouble fc) = fc
  getFC (EDoubleLit fc x) = fc
  getFC (EDoubleShow fc) = fc
  getFC (EText fc) = fc
  getFC (ETextLit fc x) = fc
  getFC (ETextAppend fc x y) = fc
  getFC (ETextShow fc) = fc
  getFC (ETextReplace fc) = fc
  getFC (EList fc) = fc
  getFC (EListLit fc x xs) = fc
  getFC (EListAppend fc x y) = fc
  getFC (EListBuild fc) = fc
  getFC (EListFold fc) = fc
  getFC (EListLength fc) = fc
  getFC (EListHead fc) = fc
  getFC (EListLast fc) = fc
  getFC (EListIndexed fc) = fc
  getFC (EListReverse fc) = fc
  getFC (EOptional fc) = fc
  getFC (ESome fc x) = fc
  getFC (ENone fc) = fc
  getFC (EEquivalent fc x y) = fc
  getFC (EAssert fc x) = fc
  getFC (ERecord fc x) = fc
  getFC (ERecordLit fc x) = fc
  getFC (EUnion fc x) = fc
  getFC (ECombine fc x y) = fc
  getFC (ECombineTypes fc x y) = fc
  getFC (EPrefer fc x y) = fc
  getFC (ERecordCompletion fc x y) = fc
  getFC (EMerge fc x y z) = fc
  getFC (EToMap fc x y) = fc
  getFC (EField fc x y) = fc
  getFC (EProject fc x y) = fc
  getFC (EWith fc x xs y) = fc
  getFC (EImportAlt fc x y) = fc
  getFC (EEmbed fc x) = fc

export
Show ImportStatement where
  show (LocalFile x) = "(LocalFile " ++ show x ++ ")"
  show (EnvVar x) = "(EnvVar " ++ x ++ ")"
  show (Http x) = "(Http " ++ x ++ ")"
  show Missing = "Missing"

export
Show (Import ImportStatement) where
  show (Raw x) = "(Raw \{show x}"
  show (Text x) = "(Text \{show x}"
  show (Location x) = "(Location \{show x}"
  show (Resolved x) = "(Resolved x)"

mutual
  export covering
  Show (Import a) where
    show (Raw x) = "(Raw)" -- TODO show x
    show (Text x) = "(Text)" -- TODO show x
    show (Location x) = "(Location)" -- TODO show x
    show (Resolved x) = "(Resolved " ++ show x ++ ")"

  export partial
  Show (Expr a) where
    show (EConst fc x) = "(EConst " ++ show x ++ ")"
    show (EVar fc x i) = "(EVar " ++ show x ++ " " ++ show i ++ ")"
    show (ELam fc x y z) = "(ELam " ++ x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (EPi fc x y z) = "(EPi " ++ x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (EApp fc x y) = "(EApp " ++ show x ++ " " ++ show y ++ ")"
    show (ELet fc x y z w) = "(ELet " ++ show x ++ " " ++ show y ++ " " ++ show z ++ " " ++ show w ++ ")"
    show (EAnnot fc x y) = "(EAnnot " ++ show x ++ " " ++ show y ++ ")"
    show (EBool fc) = "EBool"
    show (EBoolLit fc False) = "(EBoolLit False)"
    show (EBoolLit fc True) = "(EBoolLit True)"
    show (EBoolAnd fc x y) = "(EBoolAnd " ++ show x ++ " " ++ show y ++ ")"
    show (EBoolOr fc x y) = "(EBoolOr " ++ show x ++ " " ++ show y ++ ")"
    show (EBoolEQ fc x y) = "(EBoolEQ " ++ show x ++ " " ++ show y ++ ")"
    show (EBoolNE fc x y) = "(EBoolNE " ++ show x ++ " " ++ show y ++ ")"
    show (EBoolIf fc x y z) = "(EBoolIf " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (ENatural fc) = "ENatural"
    show (ENaturalLit fc k) = "(ENaturalLit " ++ show k ++ ")"
    show (ENaturalFold fc) = "ENaturalFold"
    show (ENaturalBuild fc) = "ENaturalBuild"
    show (ENaturalIsZero fc) = "ENaturalIsZero"
    show (ENaturalEven fc) = "ENaturalEven"
    show (ENaturalOdd fc) = "ENaturalOdd"
    show (ENaturalToInteger fc) = "ENaturalToInteger"
    show (ENaturalSubtract fc) = "ENaturalSubtract"
    show (ENaturalShow fc) = "NaturalShow"
    show (ENaturalPlus fc x y) = "(ENaturalPlus " ++ show x ++ " " ++ show y ++ ")"
    show (ENaturalTimes fc x y) = "(ENaturalTimes " ++ show x ++ " " ++ show y ++ ")"
    show (EInteger fc) = "EInteger"
    show (EIntegerLit fc x) = "(EIntegerLit " ++ show x ++ ")"
    show (EIntegerClamp fc) = "EIntegerClamp"
    show (EIntegerShow fc) = "EIntegerShow"
    show (EIntegerNegate fc) = "EIntegerNegate"
    show (EIntegerToDouble fc) = "EIntegerToDouble"
    show (EDouble fc) = "EDouble"
    show (EDoubleLit fc k) = "(EDoubleLit " ++ show k ++ ")"
    show (EDoubleShow fc) = "EDoubleShow"
    show (EText fc) = "EText"
    show (ETextLit fc x) = "(ETextLit " ++ show x ++ ")"
    show (ETextAppend fc x y) = "(ETextAppend " ++ show x ++ " " ++ show y ++ ")"
    show (ETextShow fc) = "ETextShow"
    show (ETextReplace fc) = "ETextReplace"
    show (EList fc) = "EList"
    show (EListLit fc Nothing xs) = "(EListLit Nothing " ++ show xs ++ ")"
    show (EListLit fc (Just x) xs) = "(EListLit (Just " ++ show x ++ ") " ++ show xs ++ ")"
    show (EListAppend fc x y) = "(EListAppend " ++ show x ++ " " ++ show y ++ ")"
    show (EListBuild fc) = "EListBuild"
    show (EListFold fc) = "EListFold"
    show (EListHead fc) = "EListHead"
    show (EListLength fc) = "EListLength"
    show (EListLast fc) = "EListLast"
    show (EListIndexed fc) = "EListIndexed"
    show (EListReverse fc) = "EListReverse"
    show (EOptional fc) = "EOptional"
    show (ENone fc) = "ENone"
    show (ESome fc x) = "(ESome " ++ show x ++ ")"
    show (EEquivalent fc x y) = "(EEquivalent " ++ show x ++ " " ++ show y ++ ")"
    show (EAssert fc x) = "(EAssert " ++ show x ++ ")"
    show (ERecord fc x) = "(ERecord " ++ show x ++ ")"
    show (ERecordLit fc x) = "(ERecordLit " ++ show x ++ ")"
    show (EUnion fc x) = "(EUnion $ " ++ show x ++ ")"
    show (ECombine fc x y) = "(ECombine " ++ show x ++ " " ++ show y ++ ")"
    show (ECombineTypes fc x y) = "(ECombineTypes " ++ show x ++ " " ++ show y ++ ")"
    show (EPrefer fc x y) = "(EPrefer " ++ show x ++ " " ++ show y ++ ")"
    show (ERecordCompletion fc x y) = "(ERecordCompletion " ++ show x ++ " " ++ show y ++ ")"
    show (EMerge fc x y z) = "(EMerge " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (EToMap fc x y) = "(EToMap " ++ show x ++ " " ++ show y ++ ")"
    show (EField fc x y) = "(EField " ++ show x ++ " " ++ show y ++ ")"
    show (EProject fc x y) = "(EProject " ++ show x ++ " " ++ show y ++ ")"
    show (EWith fc x ks y) = "(EWith " ++ show x ++ " " ++ show ks ++ " " ++ show y ++ ")"
    show (EImportAlt fc x y) = "(EImportAlt " ++ show x ++ " " ++ show y ++ ")"
    show (EEmbed fc x) = "(EEmbed " ++ show x ++ ")"

  public export covering
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
