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
    = VConst FC U
    | VVar FC Name Int
    | VPrimVar FC
    | VApp FC Value Value
    | VLambda FC Ty Closure
    | VHLam FC HLamInfo (Value -> Either Error Value)
    | VPi FC Ty Closure
    | VHPi FC Name Value (Value -> Either Error Value)

    | VBool FC
    | VBoolLit FC Bool
    | VBoolAnd FC Value Value
    | VBoolOr FC Value Value
    | VBoolEQ FC Value Value
    | VBoolNE FC Value Value
    | VBoolIf FC Value Value Value

    | VNatural FC
    | VNaturalLit FC Nat
    | VNaturalBuild FC Value
    | VNaturalFold FC Value Value Value Value
    | VNaturalIsZero FC Value
    | VNaturalEven FC Value
    | VNaturalOdd FC Value
    | VNaturalSubtract FC Value Value
    | VNaturalShow FC Value
    | VNaturalToInteger FC Value
    | VNaturalPlus FC Value Value
    | VNaturalTimes FC Value Value

    | VInteger FC
    | VIntegerLit FC Integer
    | VIntegerShow FC Value
    | VIntegerNegate FC Value
    | VIntegerClamp FC Value
    | VIntegerToDouble FC Value

    | VDouble FC
    | VDoubleLit FC Double
    | VDoubleShow FC Value

    | VText FC
    | VTextLit FC VChunks
    | VTextAppend FC Value Value
    | VTextShow FC Value
    | VTextReplace FC Value Value Value

    | VList FC Ty
    | VListLit FC (Maybe Ty) (List Value)
    | VListAppend FC Value Value
    | VListBuild FC Value Value
    | VListFold FC Value Value Value Value Value
    | VListLength FC Value Value
    | VListHead FC Value Value
    | VListLast FC Value Value
    | VListIndexed FC Value Value
    | VListReverse FC Value Value

    | VOptional FC Ty
    | VNone FC Ty
    | VSome FC Ty

    | VEquivalent FC Value Value
    | VAssert FC Value

    | VRecord FC (SortedMap FieldName Value)
    | VRecordLit FC (SortedMap FieldName Value)
    | VUnion FC (SortedMap FieldName (Maybe Value))
    | VField FC Value FieldName
    | VCombine FC Value Value
    | VCombineTypes FC Value Value
    | VPrefer FC Value Value
    | VMerge FC Value Value (Maybe Value)
    | VToMap FC Value (Maybe Value)
    -- TODO missing VField?
    | VInject FC (SortedMap FieldName (Maybe Value)) FieldName (Maybe Value) -- TODO proof that key is in SM?
    | VProject FC (Value) (Either (List FieldName) (Value))
    | VWith FC Value (List1 FieldName) Value

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
    | NaturalSubtractZero

||| Returns `VHPi "_" a (\_ => Right b)`
||| Non-dependent function arrow
public export
vFun : Value -> Value -> Value
vFun a b = VHPi initFC "_" a (\_ => Right b)

||| Returns `VHLam Prim f`
public export
VPrim : (Value -> Either Error Value) -> Value
VPrim f = VHLam initFC Prim f

mutual
  Show HLamInfo where
    show Prim = "Prim"
    show (Typed x y) = "(Typed " ++ show x ++ " " ++ show y ++ ")"
    show NaturalSubtractZero = "NaturalSubtractZero"

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
    show (VConst fc x) = "(VConst " ++ show x ++ ")"
    show (VVar fc x i) = "(VVar " ++ show x ++ " " ++ show i ++ ")"
    show (VPrimVar fc) = "VPrimVar"
    show (VApp fc x y) = "(VApp " ++ show x ++ " " ++ show y ++ ")"
    show (VLambda fc x y) = "(VLambda " ++ show x ++ " " ++ show y ++ ")"
    show (VHLam fc i x) = "(VHLam " ++ show i ++ " " ++ show (x (VPrimVar fc))
    show (VPi fc x y) = "(VPi " ++ show x ++ " " ++ show y ++ ")"
    show (VHPi fc i x y) = "(VHPi " ++ show i ++ " " ++ show x ++ show (y (VPrimVar fc))

    show (VBool fc) = "VBool"
    show (VBoolLit fc x) = "(VBoolLit " ++ show x ++ ")"
    show (VBoolAnd fc x y) = "(VBoolAnd " ++ show x ++ " " ++ show y ++ ")"
    show (VBoolOr fc x y) = "(VBoolOr " ++ show x ++ " " ++ show y ++ ")"
    show (VBoolEQ fc x y) = "(VBoolEQ " ++ show x ++ " " ++ show y ++ ")"
    show (VBoolNE fc x y) = "(VBoolNE " ++ show x ++ " " ++ show y ++ ")"
    show (VBoolIf fc x y z) = "(VBoolNE " ++ show x ++ " " ++ show y ++ " " ++ show y ++ ")"

    show (VNatural fc) = "VNatural"
    show (VNaturalLit fc k) = "(VNaturalLit " ++ show k ++ ")"
    show (VNaturalBuild fc x) = "(VNaturalBuild " ++ show x ++ ")"
    show (VNaturalFold fc w x y z) =
      "(VNaturalFold " ++ show w ++ " " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (VNaturalIsZero fc x) = "(VNaturalIsZero " ++ show x ++ ")"
    show (VNaturalEven fc x) = "(VNaturalEven " ++ show x ++ ")"
    show (VNaturalOdd fc x) = "(VNaturalOdd " ++ show x ++ ")"
    show (VNaturalToInteger fc x) = "(VNaturalToInteger " ++ show x ++ ")"
    show (VNaturalSubtract fc x y) = "(VNaturalSubtract " ++ show x ++ " " ++ show y ++ ")"
    show (VNaturalShow fc x) = "(VNaturalShow " ++ show x ++ ")"
    show (VNaturalPlus fc x y) = "(VNaturalPlus " ++ show x ++ " " ++ show y ++ ")"
    show (VNaturalTimes fc x y) = "(VNaturalTimes " ++ show x ++ " " ++ show y ++ ")"

    show (VInteger fc) = "VInteger"
    show (VIntegerLit fc x) = "(VIntegerLit " ++ show x ++ ")"
    show (VIntegerShow fc x) = "(VIntegerShow " ++ show x ++ ")"
    show (VIntegerNegate fc x) = "(VIntegerNegate " ++ show x ++ ")"
    show (VIntegerClamp fc x) = "(VIntegerClamp " ++ show x ++ ")"
    show (VIntegerToDouble fc x) = "(VIntegerToDouble " ++ show x ++ ")"

    show (VDouble fc) = "VDouble"
    show (VDoubleLit fc k) = "(VDoubleLit " ++ show k ++ ")"
    show (VDoubleShow fc x) = "(VDoubleShow " ++ show x ++ ")"

    show (VText fc) = "VText"
    show (VTextLit fc x) = "(VTextLit " ++ show x ++ ")"
    show (VTextAppend fc x y) = "(VTextAppend " ++ show x ++ " " ++ show y ++ ")"
    show (VTextShow fc x) = "(VTextShow " ++ show x ++ ")"
    show (VTextReplace fc x y z) = "(VTextReplace " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"

    show (VList fc a) = "(VList " ++ show a ++ ")"
    show (VListLit fc ty vs) = "(VListLit " ++ show ty ++ show vs ++ ")"
    show (VListAppend fc x y) = "(VListAppend " ++ show x ++ " " ++ show y ++ ")"
    show (VListBuild fc x y) = "(VListBuild " ++ show x ++ " " ++ show y ++ ")"
    show (VListFold fc v w x y z) =
      "(VListFold " ++ show v ++ " " ++ show w ++ " " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (VListLength fc x y) = "(VListLength " ++ show x ++ " " ++ show y ++ ")"
    show (VListHead fc x y) = "(VListHead " ++ show x ++ " " ++ show y ++ ")"
    show (VListLast fc x y) = "(VListLast " ++ show x ++ " " ++ show y ++ ")"
    show (VListIndexed fc x y) = "(VListIndexed " ++ show x ++ " " ++ show y ++ ")"
    show (VListReverse fc x y) = "(VListReverse " ++ show x ++ " " ++ show y ++ ")"

    show (VOptional fc a) = "(VOptional " ++ show a ++ ")"
    show (VNone fc a) = "(VNone " ++ show a ++ ")"
    show (VSome fc a) = "(VSome " ++ show a ++ ")"

    show (VEquivalent fc x y) = "(VEquivalent " ++ show x ++ " " ++ show y ++ ")"
    show (VAssert fc x) = "(VAssert " ++ show x ++ ")"

    show (VRecord fc a) = "(VRecord $ " ++ show a ++ ")"
    show (VRecordLit fc a) = "(VRecordLit $ " ++ show a ++ ")"
    show (VUnion fc a) = "(VUnion " ++ show a ++ ")"
    show (VField fc x y) = "(VField " ++ show x ++ " " ++ show y ++ ")"
    show (VCombine fc x y) = "(VCombine " ++ show x ++ " " ++ show y ++ ")"
    show (VCombineTypes fc x y) = "(VCombineTypes " ++ show x ++ " " ++ show y ++ ")"
    show (VPrefer fc x y) = "(VPrefer " ++ show x ++ " " ++ show y ++ ")"
    show (VMerge fc x y z) = "(VMerge " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (VToMap fc x y) = "(VToMap " ++ show x ++ " " ++ show y ++ ")"
    show (VInject fc a k v) = "(VInject " ++ show a ++ " " ++ show k ++ " " ++ show v ++ ")"
    show (VProject fc x y) = "(VProject " ++ show x ++ " " ++ show y ++ ")"
    show (VWith fc x ks y) = "(VWith " ++ show x ++ " " ++ show ks ++ " " ++ show y ++ ")"

public export
Semigroup VChunks where
  (<+>) (MkVChunks xys z) (MkVChunks [] z') = MkVChunks xys (z <+> z')
  (<+>) (MkVChunks xys z) (MkVChunks ((x', y') :: xys') z') = MkVChunks (xys ++ ((z <+> x', y') :: xys')) z'

public export
Monoid VChunks where
  neutral = MkVChunks neutral neutral

public export
getBounds : Value -> FC
getBounds (VConst fc x) = fc
getBounds (VVar fc x y) = fc
getBounds (VPrimVar fc) = fc
getBounds (VApp fc x y) = fc
getBounds (VLambda fc x y) = fc
getBounds (VHLam fc x f) = fc
getBounds (VPi fc x y) = fc
getBounds (VHPi fc x y f) = fc
getBounds (VBool fc) = fc
getBounds (VBoolLit fc x) = fc
getBounds (VBoolAnd fc x y) = fc
getBounds (VBoolOr fc x y) = fc
getBounds (VBoolEQ fc x y) = fc
getBounds (VBoolNE fc x y) = fc
getBounds (VBoolIf fc x y z) = fc
getBounds (VNatural fc) = fc
getBounds (VNaturalLit fc k) = fc
getBounds (VNaturalBuild fc x) = fc
getBounds (VNaturalFold fc x y z w) = fc
getBounds (VNaturalIsZero fc x) = fc
getBounds (VNaturalEven fc x) = fc
getBounds (VNaturalOdd fc x) = fc
getBounds (VNaturalSubtract fc x y) = fc
getBounds (VNaturalShow fc x) = fc
getBounds (VNaturalToInteger fc x) = fc
getBounds (VNaturalPlus fc x y) = fc
getBounds (VNaturalTimes fc x y) = fc
getBounds (VInteger fc) = fc
getBounds (VIntegerLit fc x) = fc
getBounds (VIntegerShow fc x) = fc
getBounds (VIntegerNegate fc x) = fc
getBounds (VIntegerClamp fc x) = fc
getBounds (VIntegerToDouble fc x) = fc
getBounds (VDouble fc) = fc
getBounds (VDoubleLit fc x) = fc
getBounds (VDoubleShow fc x) = fc
getBounds (VText fc) = fc
getBounds (VTextLit fc x) = fc
getBounds (VTextAppend fc x y) = fc
getBounds (VTextShow fc x) = fc
getBounds (VTextReplace fc x y z) = fc
getBounds (VList fc x) = fc
getBounds (VListLit fc x xs) = fc
getBounds (VListAppend fc x y) = fc
getBounds (VListBuild fc x y) = fc
getBounds (VListFold fc x y z w v) = fc
getBounds (VListLength fc x y) = fc
getBounds (VListHead fc x y) = fc
getBounds (VListLast fc x y) = fc
getBounds (VListIndexed fc x y) = fc
getBounds (VListReverse fc x y) = fc
getBounds (VOptional fc x) = fc
getBounds (VNone fc x) = fc
getBounds (VSome fc x) = fc
getBounds (VEquivalent fc x y) = fc
getBounds (VAssert fc x) = fc
getBounds (VRecord fc x) = fc
getBounds (VRecordLit fc x) = fc
getBounds (VUnion fc x) = fc
getBounds (VField fc x y) = fc
getBounds (VCombine fc x y) = fc
getBounds (VCombineTypes fc x y) = fc
getBounds (VPrefer fc x y) = fc
getBounds (VMerge fc x y z) = fc
getBounds (VToMap fc x y) = fc
getBounds (VInject fc x y z) = fc
getBounds (VProject fc x y) = fc
getBounds (VWith fc x xs y) = fc
