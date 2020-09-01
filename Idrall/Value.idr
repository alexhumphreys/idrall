module Idrall.Value

import Idrall.Expr

mutual
  public export
  data Normal = Normal' Ty Value

  public export
  Ty : Type
  Ty = Value

  covering
  public export
  Show Normal where
    show (Normal' x y) = "(Normal' " ++ (show x) ++ " " ++ show y ++ ")"

  public export
  Env : Type -- Now a type alias
  Env = List (Name,Value)
  %name Env env, env1, env2

  public export
  record Closure where
    constructor MkClosure
    closureEnv : Env
    closureName : Name
    closureType : Expr Void
    closureBody : Expr Void

  public export
  Show Closure where
    show (MkClosure closureEnv closureName closureType closureBody)
      = "(MkClosure " ++ show closureEnv ++ " " ++ closureName ++ " " ++ show closureType
         ++ " " ++ show closureBody ++ ")"

  -- Values
  public export
  data Value
    = VLambda Ty Closure
    | VPi Ty Closure
    | VEquivalent Value Value
    | VAssert Value
    | VConst U
    | VBool
    | VBoolLit Bool
    | VInteger
    | VIntegerLit Integer
    | VNatural
    | VNaturalLit Nat
    | VList Ty
    | VListLit (Maybe Ty) (List Value)
    | VOptional Ty
    | VNone Ty
    | VSome Ty
    | VNeutral Ty Neutral

  public export
  data Neutral
    = NVar Name
    | NNaturalIsZero Neutral
    | NIntegerNegate Neutral
    | NEquivalent Neutral Normal
    | NAssert Neutral
    | NApp Neutral Normal
    | NBoolAnd Neutral Normal
    | NList Neutral
    | NListAppend Neutral Normal
    | NListHead Neutral Normal
    | NOptional Neutral
    | NNone Neutral
    | NSome Neutral

  public export
  Show Value where
    show (VLambda x y) = "(VLambda " ++ show x ++ " " ++ show y ++ ")"
    show (VPi x y) = "(VPi " ++ show x ++ " " ++ show y ++ ")"
    show (VEquivalent x y) = "(VEquivalent " ++ show x ++ " " ++ show y ++ ")"
    show (VAssert x) = "(VEquivalent " ++ show x ++ ")"
    show (VConst x) = "(VConst " ++ show x ++ ")"
    show VBool = "VBool"
    show (VBoolLit x) = "(VBoolLit " ++ show x ++ ")"
    show VInteger = "VInteger"
    show (VIntegerLit x) = "(VIntegerLit " ++ show x ++ ")"
    show VNatural = "VNatural"
    show (VNaturalLit k) = "(VNaturalLit " ++ show k ++ ")"
    show (VList a) = "(VList " ++ show a ++ ")"
    show (VListLit ty vs) = "(VListLit " ++ show ty ++ show vs ++ ")"
    show (VOptional a) = "(VOptional " ++ show a ++ ")"
    show (VNone a) = "(VNone " ++ show a ++ ")"
    show (VSome a) = "(VSome " ++ show a ++ ")"
    show (VNeutral x y) = "(VNeutral " ++ show x ++ " " ++ show y ++ ")"

  public export
  Show Neutral where
    show (NVar x) = "(NVar " ++ show x ++ ")"
    show (NNaturalIsZero x) = "(NNaturalIsZero " ++ show x ++ ")"
    show (NIntegerNegate x) = "(NIntegerNegate " ++ show x ++ ")"
    show (NEquivalent x y) = "(NEquivalent " ++ show x ++ " " ++ show y ++ ")"
    show (NAssert x) = "(NEquivalent " ++ show x ++ ")"
    show (NApp x y) = "(NApp " ++ show x ++ " " ++ show y ++ ")"
    show (NList x) = "(NList " ++ show x ++ ")"
    show (NListAppend x y) = "(NListAppend " ++ show x ++ " " ++ show y ++ ")"
    show (NListHead x y) = "(NListHead " ++ show x ++ " " ++ show y ++ ")"
    show (NOptional x) = "(NOptional " ++ show x ++ ")"
    show (NNone x) = "(NNone " ++ show x ++ ")"
    show (NSome x) = "(NSome " ++ show x ++ ")"
    show (NBoolAnd x y) = "(NBoolAnd " ++ show x ++ " " ++ show y ++ ")"
