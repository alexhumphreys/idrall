data Expr
  -- | Lam x A b ~ λ(x : A) -> b
  = ELam String Expr Expr
  -- | > App f a ~ f a
  | EApp Expr Expr
  -- | > Let x Nothing r e ~ let x = r in e
  --   > Let x (Just t) r e ~ let x : t = r in e
  | ELet String (Maybe Expr) Expr Expr
  -- | > Annot x t ~ x : t
  | EAnnot Expr Expr
  -- | > Bool ~ Bool
  | EBool
  -- | > BoolLit b ~ b
  | EBoolLit Bool
  -- | > BoolAnd x y ~ x && y
  | BoolAnd Expr Expr
  -- | > Natural ~ Natural
  | ENatural
  -- | > NaturalLit n ~ n
  | ENaturalLit Nat
  -- | > NaturalIsZero ~ Natural/isZero
  | ENaturalIsZero Expr

mutual
  data Normal = Normal' Ty Value

  Name : Type
  Name = String

  Ty : Type
  Ty = Value

  Env : Type -- Now a type alias
  Env = List (Name,Value)
  %name Env env, env1, env2

  record Closure where
    constructor MkClosure
    closureEnv : Env
    closureName : Name
    closureBody : Expr

  -- Values
  data Value
    = VLambda Closure
    | VBool
    | VBoolLit Bool
    | VNatural
    | VNaturalLit Nat
    | VAnnot Value Ty
    | VNeutral Neutral

  data Neutral
    = NNaturalIsZero Normal -- TODO Neutral?
    | NApp Neutral Normal
    | NBoolAnd Normal Normal -- TODO Neutral Normal?
    | NLet Name
