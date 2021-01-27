module Idrall.Value

import Idrall.Expr
import Idrall.Error

import Data.List1

mutual
  public export
  Ty : Type
  Ty = Value

  -- Values
  public export
  data Value
    = VConst U
    | VVar Name Int
    | VPrimVar
    | VApp Value Value
    | VLambda Ty Closure
    | VHLam HLamInfo (Value -> Either Error Value)
    | VPi Ty Closure
    | VHPi Name Value (Value -> Either Error Value)

    | VBool
    | VBoolLit Bool
    | VBoolAnd Value Value
    | VBoolOr Value Value
    | VBoolEQ Value Value
    | VBoolNE Value Value
    | VBoolIf Value Value Value

    | VNatural
    | VNaturalLit Nat
    | VNaturalBuild Value
    | VNaturalFold Value Value Value Value
    | VNaturalIsZero Value
    | VNaturalEven Value
    | VNaturalOdd Value
    | VNaturalSubtract Value Value
    | VNaturalShow Value
    | VNaturalToInteger Value
    | VNaturalPlus Value Value
    | VNaturalTimes Value Value

    | VInteger
    | VIntegerLit Integer
    | VIntegerShow Value
    | VIntegerNegate Value
    | VIntegerClamp Value
    | VIntegerToDouble Value

    | VDouble
    | VDoubleLit Double
    | VDoubleShow Value

    | VText
    | VTextLit VChunks
    | VTextAppend Value Value
    | VTextShow Value
    | VTextReplace Value Value Value

    | VList Ty
    | VListLit (Maybe Ty) (List Value)
    | VListAppend Value Value
    | VListBuild Value Value
    | VListFold Value Value Value Value Value
    | VListLength Value Value
    | VListHead Value Value
    | VListLast Value Value
    | VListIndexed Value Value
    | VListReverse Value Value

    | VOptional Ty
    | VNone Ty
    | VSome Ty

    | VEquivalent Value Value
    | VAssert Value

    | VRecord (SortedMap FieldName Value)
    | VRecordLit (SortedMap FieldName Value)
    | VUnion (SortedMap FieldName (Maybe Value))
    | VField Value FieldName
    | VCombine Value Value
    | VCombineTypes Value Value
    | VPrefer Value Value
    | VMerge Value Value (Maybe Value)
    | VToMap Value (Maybe Value)
    -- TODO missing VField?
    | VInject (SortedMap FieldName (Maybe Value)) FieldName (Maybe Value) -- TODO proof that key is in SM?
    | VProject (Value) (Either (List FieldName) (Value))
    | VWith Value (List1 FieldName) Value

  public export
  data Env
    = Empty
    | Skip Env Name
    | Extend Env Name Value

  public export
  data VChunks = MkVChunks (List (String, Value)) String

  public export
  record Closure where
    constructor MkClosure
    closureName : Name
    closureEnv : Env
    closureBody : Expr Void

  public export
  data HLamInfo
    = Prim
    | Typed String Value
    | NaturalFoldCl Value
    | ListFoldCl Value

||| Returns `VHPi "_" a (\_ => Right b)`
||| Non-dependent function arrow
public export
vFun : Value -> Value -> Value
vFun a b = VHPi "_" a (\_ => Right b)

||| Returns `VHLam Prim f`
public export
VPrim : (Value -> Either Error Value) -> Value
VPrim f = VHLam Prim f

mutual
  Show HLamInfo where
    show Prim = "Prim"
    show (Typed x y) = "(Typed " ++ show x ++ " " ++ show y ++ ")"
    show (ListFoldCl x) = "(ListFoldCl " ++ show x ++ ")"
    show (NaturalFoldCl x) = "(NaturalFoldCl " ++ show x ++ ")"

  public export
  Show Env where
    show Empty = "Empty"
    show (Skip x y) = "(Skip " ++ show x ++ " " ++ show y ++ ")"
    show (Extend x y z) = "(Extend " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"

  public export
  Show Closure where
    show (MkClosure closureName closureEnv closureBody)
      = "(MkClosure " ++ show closureName ++ " " ++ show closureEnv ++ " " ++ show closureBody ++ ")"

  public export
  Show VChunks where
    show (MkVChunks xs x) = "(MkVChunks " ++ show xs ++ " " ++ show x ++ ")"

  public export
  Show Value where
    show (VConst x) = "(VConst " ++ show x ++ ")"
    show (VVar x i) = "(VVar " ++ show x ++ " " ++ show i ++ ")"
    show (VPrimVar) = "VPrimVar"
    show (VApp x y) = "(VApp " ++ show x ++ " " ++ show y ++ ")"
    show (VLambda x y) = "(VLambda " ++ show x ++ " " ++ show y ++ ")"
    show (VHLam i x) = "(VHLam " ++ show i ++ " " ++ show (x VPrimVar)
    show (VPi x y) = "(VPi " ++ show x ++ " " ++ show y ++ ")"
    show (VHPi i x y) = "(VHPi " ++ show i ++ " " ++ show x ++ show (y VPrimVar)

    show VBool = "VBool"
    show (VBoolLit x) = "(VBoolLit " ++ show x ++ ")"
    show (VBoolAnd x y) = "(VBoolAnd " ++ show x ++ " " ++ show y ++ ")"
    show (VBoolOr x y) = "(VBoolOr " ++ show x ++ " " ++ show y ++ ")"
    show (VBoolEQ x y) = "(VBoolEQ " ++ show x ++ " " ++ show y ++ ")"
    show (VBoolNE x y) = "(VBoolNE " ++ show x ++ " " ++ show y ++ ")"
    show (VBoolIf x y z) = "(VBoolNE " ++ show x ++ " " ++ show y ++ " " ++ show y ++ ")"

    show VNatural = "VNatural"
    show (VNaturalLit k) = "(VNaturalLit " ++ show k ++ ")"
    show (VNaturalBuild x) = "(VNaturalBuild " ++ show x ++ ")"
    show (VNaturalFold w x y z) =
      "(VNaturalFold " ++ show w ++ " " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (VNaturalIsZero x) = "(VNaturalIsZero " ++ show x ++ ")"
    show (VNaturalEven x) = "(VNaturalEven " ++ show x ++ ")"
    show (VNaturalOdd x) = "(VNaturalOdd " ++ show x ++ ")"
    show (VNaturalToInteger x) = "(VNaturalToInteger " ++ show x ++ ")"
    show (VNaturalSubtract x y) = "(VNaturalSubtract " ++ show x ++ " " ++ show y ++ ")"
    show (VNaturalShow x) = "(VNaturalShow " ++ show x ++ ")"
    show (VNaturalPlus x y) = "(VNaturalPlus " ++ show x ++ " " ++ show y ++ ")"
    show (VNaturalTimes x y) = "(VNaturalTimes " ++ show x ++ " " ++ show y ++ ")"

    show VInteger = "VInteger"
    show (VIntegerLit x) = "(VIntegerLit " ++ show x ++ ")"
    show (VIntegerShow x) = "(VIntegerShow " ++ show x ++ ")"
    show (VIntegerNegate x) = "(VIntegerNegate " ++ show x ++ ")"
    show (VIntegerClamp x) = "(VIntegerClamp " ++ show x ++ ")"
    show (VIntegerToDouble x) = "(VIntegerToDouble " ++ show x ++ ")"

    show VDouble = "VDouble"
    show (VDoubleLit k) = "(VDoubleLit " ++ show k ++ ")"
    show (VDoubleShow x) = "(VDoubleShow " ++ show x ++ ")"

    show (VText) = "VText"
    show (VTextLit x) = "(VTextLit " ++ show x ++ ")"
    show (VTextAppend x y) = "(VTextAppend " ++ show x ++ " " ++ show y ++ ")"
    show (VTextShow x) = "(VTextShow " ++ show x ++ ")"
    show (VTextReplace x y z) = "(VTextReplace " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"

    show (VList a) = "(VList " ++ show a ++ ")"
    show (VListLit ty vs) = "(VListLit " ++ show ty ++ show vs ++ ")"
    show (VListAppend x y) = "(VListAppend " ++ show x ++ " " ++ show y ++ ")"
    show (VListBuild x y) = "(VListBuild " ++ show x ++ " " ++ show y ++ ")"
    show (VListFold v w x y z) =
      "(VListFold " ++ show v ++ " " ++ show w ++ " " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (VListLength x y) = "(VListLength " ++ show x ++ " " ++ show y ++ ")"
    show (VListHead x y) = "(VListHead " ++ show x ++ " " ++ show y ++ ")"
    show (VListLast x y) = "(VListLast " ++ show x ++ " " ++ show y ++ ")"
    show (VListIndexed x y) = "(VListIndexed " ++ show x ++ " " ++ show y ++ ")"
    show (VListReverse x y) = "(VListReverse " ++ show x ++ " " ++ show y ++ ")"

    show (VOptional a) = "(VOptional " ++ show a ++ ")"
    show (VNone a) = "(VNone " ++ show a ++ ")"
    show (VSome a) = "(VSome " ++ show a ++ ")"

    show (VEquivalent x y) = "(VEquivalent " ++ show x ++ " " ++ show y ++ ")"
    show (VAssert x) = "(VAssert " ++ show x ++ ")"

    show (VRecord a) = "(VRecord $ " ++ show a ++ ")"
    show (VRecordLit a) = "(VRecordLit $ " ++ show a ++ ")"
    show (VUnion a) = "(VUnion " ++ show a ++ ")"
    show (VField x y) = "(VField " ++ show x ++ " " ++ show y ++ ")"
    show (VCombine x y) = "(VCombine " ++ show x ++ " " ++ show y ++ ")"
    show (VCombineTypes x y) = "(VCombineTypes " ++ show x ++ " " ++ show y ++ ")"
    show (VPrefer x y) = "(VPrefer " ++ show x ++ " " ++ show y ++ ")"
    show (VMerge x y z) = "(VMerge " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (VToMap x y) = "(VToMap " ++ show x ++ " " ++ show y ++ ")"
    show (VInject a k v) = "(VInject " ++ show a ++ " " ++ show k ++ " " ++ show v ++ ")"
    show (VProject x y) = "(VProject " ++ show x ++ " " ++ show y ++ ")"
    show (VWith x ks y) = "(VWith " ++ show x ++ " " ++ show ks ++ " " ++ show y ++ ")"

public export
Semigroup VChunks where
  (<+>) (MkVChunks xys z) (MkVChunks [] z') = MkVChunks xys (z <+> z')
  (<+>) (MkVChunks xys z) (MkVChunks ((x', y') :: xys') z') = MkVChunks (xys ++ ((z <+> x', y') :: xys')) z'

public export
Monoid VChunks where
  neutral = MkVChunks neutral neutral
