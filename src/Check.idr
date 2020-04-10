Namespace : Type
Namespace = List (String, Integer)
%name Namespace ns1, ns2, ns3

-- expressions

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

-- alpha equivalence
aEquivHelper : (i : Integer) ->
               Namespace -> Expr ->
               Namespace -> Expr ->
               Bool
aEquivHelper i ns1 (ELam x ty1 body1) ns2 (ELam y ty2 body2)
  = let newNs1 = (x, i) :: ns1
        newNs2 = (y, i) :: ns2 in
    aEquivHelper i ns1 ty1 ns2 ty2 &&
    aEquivHelper (i+1) newNs1 body1 newNs2 body2
aEquivHelper i ns1 (EApp rator1 rand1) ns2 (EApp rator2 rand2)
  = aEquivHelper i ns1 rator1 ns2 rator2 &&
    aEquivHelper i ns1 rand1 ns2 rand2
aEquivHelper i ns1 (ELet x1 t1 r1 e1) ns2 (ELet x2 t2 r2 e2) -- TODO double check this one
  = let newNs1 = (x1, i) :: ns1
        newNs2 = (x2, i) :: ns2 in
    aEquivMaybe t1 t2 &&
    aEquivHelper i ns1 r1 ns2 r2 &&
    aEquivHelper i newNs1 e1 newNs2 e2
  where
    aEquivMaybe : Maybe Expr -> Maybe Expr -> Bool
    aEquivMaybe (Just a) (Just b) = aEquivHelper i ns1 a ns2 b
    aEquivMaybe Nothing Nothing = True
    aEquivMaybe _ _ = False
aEquivHelper i ns1 (EAnnot w x) ns2 (EAnnot y z)
  = aEquivHelper i ns1 w ns2 y &&
    aEquivHelper i ns1 x ns2 z
aEquivHelper _ _ EBool _ EBool = True
aEquivHelper i ns1 (EBoolLit x) ns2 (EBoolLit y) = x == y
aEquivHelper i ns1 (BoolAnd w x) ns2 (BoolAnd y z)
  = aEquivHelper i ns1 w ns2 y &&
    aEquivHelper i ns1 x ns2 z
aEquivHelper _ _ ENatural _ ENatural = True
aEquivHelper i ns1 (ENaturalLit x) ns2 (ENaturalLit y) = x == y
aEquivHelper i ns1 (ENaturalIsZero x) ns2 (ENaturalIsZero y)
  = aEquivHelper i ns1 x ns2 y
aEquivHelper _ _ _ _ _ = False

aEquiv : Expr -> Expr -> Bool
aEquiv e1 e2 = aEquivHelper 0 [] e1 [] e2

-- values
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
    = NNaturalIsZero Neutral
    | NApp Neutral Normal
    | NBoolAnd Neutral Neutral
    | NLet Name
