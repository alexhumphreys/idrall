module Idrall.Value

import Idrall.Expr
import Idrall.Error

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
    | VNaturalIsZero Value
    | VNaturalEven Value
    | VNaturalOdd Value
    | VNaturalToInteger Value
    | VNaturalPlus Value Value
    | VNaturalTimes Value Value

    | VInteger
    | VIntegerLit Integer
    | VIntegerNegate Value

    | VDouble
    | VDoubleLit Double

    | VText
    | VTextLit VChunks

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
    | VCombine Value Value
    | VCombineTypes Value Value
    | VPrefer Value Value
    | VMerge Value Value (Maybe Value)
    | VInject (SortedMap FieldName (Maybe Value)) FieldName (Maybe Value) -- TODO proof that key is in SM?

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
    show (VHLam i x) = "(VHLam " ++ show i ++ " " ++ "TODO find some way to show VHLam arg" ++ ")"
    show (VPi x y) = "(VPi " ++ show x ++ " " ++ show y ++ ")"
    show (VHPi i x y) = "(VHPi " ++ show i ++ " " ++ show x ++ "TODO find some way to show VHPi arg" ++ ")"

    show VBool = "VBool"
    show (VBoolLit x) = "(VBoolLit " ++ show x ++ ")"
    show (VBoolAnd x y) = "(VBoolAnd " ++ show x ++ " " ++ show y ++ ")"
    show (VBoolOr x y) = "(VBoolOr " ++ show x ++ " " ++ show y ++ ")"
    show (VBoolEQ x y) = "(VBoolEQ " ++ show x ++ " " ++ show y ++ ")"
    show (VBoolNE x y) = "(VBoolNE " ++ show x ++ " " ++ show y ++ ")"
    show (VBoolIf x y z) = "(VBoolNE " ++ show x ++ " " ++ show y ++ " " ++ show y ++ ")"

    show VNatural = "VNatural"
    show (VNaturalLit k) = "(VNaturalLit " ++ show k ++ ")"
    show (VNaturalIsZero x) = "(VNaturalIsZero " ++ show x ++ ")"
    show (VNaturalEven x) = "(VNaturalEven " ++ show x ++ ")"
    show (VNaturalOdd x) = "(VNaturalOdd " ++ show x ++ ")"
    show (VNaturalToInteger x) = "(VNaturalToInteger " ++ show x ++ ")"
    show (VNaturalPlus x y) = "(VNaturalPlus " ++ show x ++ " " ++ show y ++ ")"
    show (VNaturalTimes x y) = "(VNaturalTimes " ++ show x ++ " " ++ show y ++ ")"

    show VInteger = "VInteger"
    show (VIntegerLit x) = "(VIntegerLit " ++ show x ++ ")"
    show (VIntegerNegate x) = "(VIntegerNegate " ++ show x ++ ")"

    show VDouble = "VDouble"
    show (VDoubleLit k) = "(VDoubleLit " ++ show k ++ ")"

    show (VText) = "VText"
    show (VTextLit x) = "(VTextLit " ++ show x ++ ")"

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
    show (VCombine x y) = "(VCombine " ++ show x ++ " " ++ show y ++ ")"
    show (VCombineTypes x y) = "(VCombineTypes " ++ show x ++ " " ++ show y ++ ")"
    show (VPrefer x y) = "(VPrefer " ++ show x ++ " " ++ show y ++ ")"
    show (VMerge x y z) = "(VMerge " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (VInject a k v) = "(VInject " ++ show a ++ " " ++ show k ++ " " ++ show v ++ ")"

public export
Semigroup VChunks where
  (<+>) (MkVChunks xys z) (MkVChunks [] z') = MkVChunks xys (z <+> z')
  (<+>) (MkVChunks xys z) (MkVChunks ((x', y') :: xys') z') = MkVChunks (xys ++ ((z <+> x', y') :: xys')) z'

public export
Monoid VChunks where
  neutral = MkVChunks neutral neutral
