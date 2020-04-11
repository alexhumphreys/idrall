Name : Type
Name = String

Namespace : Type
Namespace = List (Name, Integer)
%name Namespace ns1, ns2, ns3

-- expressions

data Expr
  -- x
  = EVar Name
  -- | Lam x A b ~ λ(x : A) -> b
  | ELam Name Expr Expr
  -- | > App f a ~ f a
  | EApp Expr Expr
  -- | > Let x Nothing r e ~ let x = r in e
  --   > Let x (Just t) r e ~ let x : t = r in e
  | ELet Name (Maybe Expr) Expr Expr
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
aEquivHelper i ns1 (EVar x) ns2 (EVar y) =
  case (lookup x ns1, lookup y ns2) of
       (Nothing, Nothing) => x == y
       (Just j, Just k) => i == j
       _ => False
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
    | VNeutral Ty Neutral

  data Neutral
    = NVar Name
    | NNaturalIsZero Neutral
    | NApp Neutral Normal
    | NBoolAnd Neutral Neutral
    | NLet Name

extendEnv : Env -> Name -> Value -> Env
extendEnv env x v = ((x, v) :: env)

-- definitions and dependent types
data CtxEntry = Def Ty Value | IsA Ty

Ctx : Type
Ctx = List (Name, CtxEntry)
%name Ctx ctx, ctx1, ctx2

initCtx : Ctx
initCtx = []

ctxNames : Ctx -> List Name
ctxNames ctx = map fst ctx

extendCtx : Ctx -> Name -> Ty -> Ctx
extendCtx ctx x t = (x, (IsA t)) :: ctx

define : Ctx -> Name -> Ty -> Value -> Ctx
define ctx x t v = (x, Def t v) :: ctx

mkEnv : Ctx -> Env
mkEnv [] = []
mkEnv ((x, e) :: ctx) =
  let env = mkEnv ctx in
  (case e of
        (Def _ v) => (x, v) :: env
        (IsA t) => let v = VNeutral t (NVar x) in
                       (x, v) :: env)
