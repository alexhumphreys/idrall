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

Show U where
  show CType = "Type"
  show Sort = "Sort"
  show Kind = "Kind"
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

Show Expr where

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

  Show Normal where
    show (Normal' x y) = "(normal v: " ++ (show y) ++ ")"

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

  Show Closure where

  -- Values
  data Value
    = VLambda Ty Closure
    | VPi Ty Closure
    | VConst U
    | VBool
    | VBoolLit Bool
    | VNatural
    | VNaturalLit Nat
    | VNeutral Ty Neutral

  data Neutral
    = NVar Name
    | NNaturalIsZero Neutral
    | NApp Neutral Normal
    | NBoolAnd Neutral Normal

  Show Value where
    show (VLambda x y) = "(lam " ++ show x ++ ")" -- TODO show y
    show (VPi x y) = "(pi " ++ show x ++ ")" -- TODO show y
    show (VConst x) = show x
    show VBool = "VBool"
    show (VBoolLit x) = "(V" ++ show x ++ ")"
    show VNatural = "VNatural"
    show (VNaturalLit k) = "(" ++ show k ++ ")"
    show (VNeutral x y) = ?Show_rhs_9

Show Neutral where
  show (NVar x) = x
  show (NNaturalIsZero x) = "NNaturalIsZero " ++ show x
  show (NApp x y) = ?bar_3
  show (NBoolAnd x y) = ?bar_4

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
  | EvalNaturalIsZeroErr String
  | EvalBoolAndErr
  | EvalApplyErr
  | Unexpected String Value
  | ErrorMessage String
  | SortError

Show Error where
  show (MissingVar x) = "MissingVar: " ++ show x
  show (EvalNaturalIsZeroErr x) = "EvalNaturalIsZero error:" ++ x
  show EvalBoolAndErr = "EvalBoolAndErr"
  show EvalApplyErr = "EvalApplyErr"
  show (Unexpected str v) = "Unexpected: " ++ str ++ " value: " ++ show v
  show (ErrorMessage x) = "ErrorMessage: " ++ show x
  show SortError = "SortError"

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
  eval env (ELam x ty body)
    = do vTy <- eval env ty
         Right (VLambda vTy (MkClosure env x ty body))
  eval env (EApp rator rand)
    = do rator' <- eval env rator
         rand' <- eval env rand
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
         Right x' -- TODO check this
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
  doApply (VLambda ty closure) arg =
    evalClosure closure arg
  doApply (VNeutral (VPi dom ran) neu) arg =
    do arg' <- evalClosure ran arg
       Right (VNeutral arg' (NApp neu (Normal' dom arg)))
  doApply _ _ = Left EvalApplyErr

  doNaturalIsZero : Value -> Either Error Value
  doNaturalIsZero (VNaturalLit k) = Right (VBoolLit (k == 0))
  doNaturalIsZero (VNeutral VNatural neu) = Right (VNeutral VBool (NNaturalIsZero neu))
  doNaturalIsZero x = Left (EvalNaturalIsZeroErr (show x))

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
  partial
  readBackNeutral : Ctx -> Neutral -> Either Error Expr
  readBackNeutral ctx (NVar x) = Right (EVar x)
  readBackNeutral ctx (NNaturalIsZero x) = do
    x' <- readBackNeutral ctx x
    Right (ENaturalIsZero x')
  readBackNeutral ctx (NApp neu arg) = do
      neu' <- readBackNeutral ctx neu
      arg' <- readBackNormal ctx arg
      Right (EApp neu' arg')
  readBackNeutral ctx (NBoolAnd x y) = do
    x' <- readBackNeutral ctx x
    y' <- readBackNormal ctx y
    Right (EBoolAnd x' y')

  partial
  readBackTyped : Ctx -> Ty -> Value -> Either Error Expr
  readBackTyped ctx (VPi dom ran) fun =
    let x = freshen (ctxNames ctx) (closureName ran)
        xVal = VNeutral dom (NVar x)
        ctx' = extendCtx ctx x dom in
    do ty' <- evalClosure ran xVal
       v' <- doApply fun xVal
       body <- readBackTyped ctx' ty' v'
       eTy <- readBackTyped ctx' (VConst CType) ty' -- TODO check this
       Right (ELam x eTy body)
  readBackTyped ctx (VConst x) (VConst y) = Right (EConst y) -- TODO check this
  readBackTyped ctx (VConst CType) VBool = Right EBool
  readBackTyped ctx (VConst CType) VNatural = Right ENatural
  readBackTyped ctx VBool (VBoolLit x) = Right (EBoolLit x)
  readBackTyped ctx VNatural (VNaturalLit x) = Right (ENaturalLit x)
  readBackTyped ctx t (VNeutral x z) = readBackNeutral ctx z

  partial
  readBackNormal : Ctx -> Normal -> Either Error Expr
  readBackNormal ctx (Normal' t v) = readBackTyped ctx t v

-- helpers
unexpected : Ctx -> String -> Value -> Either Error a
unexpected ctx str v = Left (Unexpected str v) -- TODO add value

isPi : Ctx -> Value -> Either Error (Ty, Closure)
isPi _ (VPi a b) = Right (a, b)
isPi ctx other = unexpected ctx "Not a Pi type" other

isNat : Ctx -> Value -> Either Error ()
isNat _ VNatural = Right ()
isNat ctx other = unexpected ctx "Not Natural" other

isBool : Ctx -> Value -> Either Error ()
isBool _ VBool = Right ()
isBool ctx other = unexpected ctx "Not Bool" other

lookupType : Ctx -> Name -> Either Error Ty -- didn't use message type
lookupType [] x = Left (ErrorMessage ("unbound variable: " ++ x))
lookupType ((y, e) :: ctx) x =
  (case x == y of
        False => lookupType ctx x
        True => (case e of
                      (Def t _) => Right t
                      (IsA t) => Right t))

axioms : (x : U) -> Either Error Value
axioms CType = Right (VConst Kind) -- TODO double check
axioms Kind = Right (VConst Sort)
axioms Sort = Left SortError

mutual
  partial
  convert : Ctx -> Ty -> Value -> Value -> Either Error ()
  convert ctx t v1 v2
    = do e1 <- readBackTyped ctx t v1
         e2 <- readBackTyped ctx t v2
         if aEquiv e1 e2
            then Right ()
            else Left (ErrorMessage "not alpha equivalent")

  partial
  check : Ctx -> Expr -> Ty -> Either Error ()
  check ctx (EConst x) t = ?check_rhs_2
  check ctx (ELam x ty body) t
    = do (a,b) <- isPi ctx t
         check ctx ty a
         xV <- evalClosure b (VNeutral a (NVar x))
         check (extendCtx ctx x a) body xV
  check ctx (EAnnot x y) t = ?check_rhs_7
  check ctx (EBoolLit x) t = isBool ctx t
  check ctx (ENaturalLit k) t = isNat ctx t
  check ctx other t
    = do t' <- synth ctx other
         convert ctx (VConst CType) t' t

  partial
  synth : Ctx -> Expr -> Either Error Ty
  synth ctx (EVar x) = lookupType ctx x
  synth ctx (EConst x) = axioms x
  synth ctx (EPi x y z) = ?synth_rhs_3
  synth ctx (ELam x ty b)
    = do xTy <- eval (mkEnv ctx) ty
         bTy <- synth (extendCtx ctx x xTy) b
         Right (VPi xTy (MkClosure (mkEnv ctx) x ty b))
  synth ctx (EApp rator rand)
    = do funTy <- synth ctx rator
         (a, b) <- isPi ctx funTy
         check ctx rand a
         synth (extendCtx ctx (closureName b) a) (closureBody b) -- TODO check why paper is different
  synth ctx (ELet x ann v e)
    = case ann of
           Nothing =>
              do xTy <- synth ctx v
                 synth (extendCtx ctx x xTy) e
           (Just ann') =>
              do check ctx ann' (VConst CType)
                 xTy <- eval (mkEnv ctx) ann'
                 check ctx v xTy
                 synth (extendCtx ctx x xTy) e
  synth ctx (EAnnot e t)
    = do tV <- synth ctx t
         check ctx e tV
         Right tV
  synth ctx EBool = Right (VConst CType)
  synth ctx (EBoolLit x) = Right (VBool)
  synth ctx (EBoolAnd x y)
    = do check ctx x VBool
         check ctx y VBool
         Right (VBool)
  synth ctx ENatural = Right (VConst CType)
  synth ctx (ENaturalLit k) = Right (VNatural)
  synth ctx (ENaturalIsZero x)
    = do check ctx x VNatural
         Right (VBool)
