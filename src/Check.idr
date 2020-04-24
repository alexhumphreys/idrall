Name : Type
Name = String

Namespace : Type
Namespace = List (Name, Integer)
%name Namespace ns1, ns2, ns3

data U = CType | Sort | Kind

Eq U where
  (==) CType CType = True
  (==) Sort Sort = True
  (==) Kind Kind = True
  (==) _ _ = False

-- expressions

data Expr
  -- x
  = EVar Name
  | EConst U
  | EPi Name Expr Expr
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
  | EBoolAnd Expr Expr
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
aEquivHelper i ns1 (EPi x a1 r1) ns2 (EPi y a2 r2) =
  aEquivHelper i ns1 a1 ns2 a2 &&
  aEquivHelper (i+1) ((x, i) :: ns1) r1 ((y, i) :: ns2) r2
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
aEquivHelper i ns1 (EBoolAnd w x) ns2 (EBoolAnd y z)
  = aEquivHelper i ns1 w ns2 y &&
    aEquivHelper i ns1 x ns2 z
aEquivHelper _ _ ENatural _ ENatural = True
aEquivHelper _ _ (EConst x) _ (EConst y) = x == y
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
    closureType : Expr
    closureBody : Expr

  -- Values
  data Value
    = VLambda Closure
    | VPi Ty Closure
    | VConst U
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
    | NBoolAnd Neutral Normal

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

-- evaluator
data Error
  = MissingVar String
  | EvalNaturalIsZeroErr
  | EvalBoolAndErr
  | EvalApplyErr

mutual
  partial
  evalClosure : Closure -> Value -> Either Error Value
  evalClosure (MkClosure env x ty e) v
    = do ty' <- eval env ty -- TODO not using this type info
         eval (extendEnv env x v) e

  evalVar : Env -> Name -> Either Error Value
  evalVar [] x = Left (MissingVar (x ++ " not found in env"))
  evalVar ((y, v) :: env) x
    = case x == y of
           True => Right v
           False => evalVar env x

  partial
  eval : Env -> Expr -> Either Error Value
  eval env (EConst x) = Right (VConst x)
  eval env (EVar x)
    = evalVar env x
  eval env (EPi x dom ran)
    = do ty <- eval env dom
         Right (VPi ty (MkClosure env x dom ran)) -- TODO double check
  eval env (ELam x ty body) = Right (VLambda (MkClosure env x ty body))
  eval env (EApp rator rand)
    = do rator' <- eval env rator
         rand' <- eval env rator
         doApply rator' rand'
  eval env (ELet x ty r e)
    = case ty of
           Nothing => do vr <- eval env r
                         eval (extendEnv env x vr) e
           (Just ty') => do vTy <- eval env ty' -- TODO not using this type info
                            vr <- eval env r
                            eval (extendEnv env x vr) e -- TODO change Env to use Binding?
  eval env (EAnnot x y)
    = do x' <- eval env x
         y' <- eval env y
         Right (VAnnot x' y')
  eval env EBool = Right VBool
  eval env (EBoolLit x) = Right (VBoolLit x)
  eval env (EBoolAnd x y)
    = do x' <- eval env x
         y' <- eval env y
         doBoolAnd x' y'
  eval env ENatural = Right VNatural
  eval env (ENaturalLit k) = Right (VNaturalLit k)
  eval env (ENaturalIsZero x)
    = do x' <- eval env x
         doNaturalIsZero x'

  partial
  doApply : Value -> Value -> Either Error Value
  doApply (VLambda closure) arg =
    evalClosure closure arg
  doApply (VNeutral (VPi dom ran) neu) arg =
    do arg' <- evalClosure ran arg
       Right (VNeutral arg' (NApp neu (Normal' dom arg)))
  doApply _ _ = Left EvalApplyErr

  doNaturalIsZero : Value -> Either Error Value
  doNaturalIsZero (VNaturalLit k) = Right (VBoolLit (k == 0))
  doNaturalIsZero (VNeutral VNatural neu) = Right (VNeutral VBool (NNaturalIsZero neu))
  doNaturalIsZero _ = Left EvalNaturalIsZeroErr

  doBoolAnd : Value -> Value -> Either Error Value
  doBoolAnd (VBoolLit x) (VBoolLit y) = Right (VBoolLit (x && y))
  doBoolAnd (VNeutral VBool v) y = Right (VNeutral VBool (NBoolAnd v (Normal' VBool y)))
  doBoolAnd _ _ = Left EvalBoolAndErr

-- fresh names
nextName : Name -> Name
nextName x = x ++ "'"

-- TODO could possibly fail for a list like [n', n'', n']
freshen : List Name -> Name -> Name
freshen [] n = n
freshen (x :: used) n = case x == n of
                             False => freshen used n
                             True => freshen used (nextName n)

-- reading back
mutual
  readBackNeutral : Ctx -> Neutral -> Either Error Expr
  readBackNeutral ctx (NVar x) = Right (EVar x)
  readBackNeutral ctx (NNaturalIsZero x) = do
    x' <- readBackNeutral ctx x
    Right (ENaturalIsZero x')
  readBackNeutral ctx (NApp x y) = ?readBackNeutral_rhs_3
  readBackNeutral ctx (NBoolAnd x y) = do
    x' <- readBackNeutral ctx x
    y' <- readBackNormal ctx y
    Right (EBoolAnd x' y')

  readBackTyped : Ctx -> Ty -> Value -> Either Error Expr
  readBackTyped ctx (VLambda x) y = ?readBackTyped_rhs_1
  readBackTyped ctx (VPi x z) y = ?readBackTyped_rhs_2
  readBackTyped ctx (VConst x) (VConst y) = Right (EConst y) -- TODO check this
  readBackTyped ctx (VConst CType) VBool = Right EBool
  readBackTyped ctx (VConst CType) VNatural = Right ENatural
  readBackTyped ctx VBool (VBoolLit x) = Right (EBoolLit x)
  readBackTyped ctx VNatural (VNaturalLit x) = Right (ENaturalLit x)
  readBackTyped ctx (VAnnot x z) y = ?readBackTyped_rhs_8
  readBackTyped ctx (VNeutral x z) y = ?readBackTyped_rhs_9

  readBackNormal : Ctx -> Normal -> Either Error Expr
  readBackNormal ctx (Normal' x y) = ?readBackNormal_rhs_1
