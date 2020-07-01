module Idrall.Check

import Idrall.Expr
import Idrall.Error
import Idrall.Value

%default covering

mapListEither : List a -> (a -> Either e b) -> Either e (List b)
mapListEither [] f = Right []
mapListEither (x :: xs) f =
  do rest <- mapListEither xs f
     x' <- f x
     Right (x' :: rest)

-- alpha equivalence
mutual
  total
  aEquivHelper : (i : Integer) ->
                 Namespace -> Expr Void ->
                 Namespace -> Expr Void ->
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
      aEquivMaybe i ns1 t1 ns2 t2 &&
      aEquivHelper i ns1 r1 ns2 r2 &&
      aEquivHelper i newNs1 e1 newNs2 e2
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
  aEquivHelper i ns1 (EEquivalent w x) ns2 (EEquivalent y z)
    = aEquivHelper i ns1 w ns1 x &&
      aEquivHelper i ns1 w ns2 y &&
      aEquivHelper i ns2 y ns2 z
  aEquivHelper i ns1 (EAssert x) ns2 (EAssert y)
    = aEquivHelper i ns1 x ns2 y
  aEquivHelper i ns1 (EList x) ns2 (EList y)
    = aEquivHelper i ns1 x ns2 y
  aEquivHelper i ns1 (EListLit tx xs) ns2 (EListLit ty ys)
    = aEquivMaybe i ns1 tx ns2 ty &&
      aEquivList i ns1 xs ns2 ys
  aEquivHelper i ns1 (EListAppend w x) ns2 (EListAppend y z)
    = aEquivHelper i ns1 w ns2 y &&
      aEquivHelper i ns1 x ns2 z
  aEquivHelper _ _ _ _ _ = False
  -- TODO check if assert/equivalent should be in here

  aEquivMaybe : (i : Integer) ->
                Namespace -> Maybe (Expr Void) ->
                Namespace -> Maybe (Expr Void) -> Bool
  aEquivMaybe i ns1 (Just a) ns2 (Just b) = aEquivHelper i ns1 a ns2 b
  aEquivMaybe _ _ Nothing _ Nothing = True
  aEquivMaybe _ _ _ _ _ = False

  aEquivList : (i : Integer) ->
                Namespace -> List (Expr Void) ->
                Namespace -> List (Expr Void) -> Bool
  aEquivList i ns1 [] ns2 [] = True
  aEquivList i ns1 (x :: xs) ns2 (y :: ys) =
    aEquivHelper i ns1 x ns2 y &&
    aEquivList i ns1 xs ns2 ys
  aEquivList i ns1 _ ns2 _ = False

aEquiv : Expr Void -> Expr Void -> Bool
aEquiv e1 e2 = aEquivHelper 0 [] e1 [] e2

-- env
export
initEnv : Env
initEnv = []

extendEnv : Env -> Name -> Value -> Env
extendEnv env x v = ((x, v) :: env)

-- definitions and dependent types
data CtxEntry = Def Ty Value | IsA Ty

export
Ctx : Type
Ctx = List (Name, CtxEntry)
%name Ctx ctx, ctx1, ctx2

export
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

  export
  partial
  eval : Env -> Expr Void -> Either Error Value
  eval env (EConst x) = Right (VConst x)
  eval env (EVar x)
    = evalVar env x
  eval env (EPi x dom ran)
    = do ty <- eval env dom
         Right (VPi ty (MkClosure env x dom ran)) -- TODO double check
  eval env (ELam x ty body)
    = do vTy <- eval env ty
         Right (VLambda vTy (MkClosure env x ty body))
  eval env (EEquivalent x y) =
    do xV <- eval env x
       yV <- eval env y
       Right (VEquivalent xV yV)
  eval env (EAssert x) = do
    xV <- eval env x
    doAssert xV
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
  eval env (EList a) = do
    a' <- eval env a
    Right (VList a')
  eval env (EListLit Nothing es) = do
    vs <- mapListEither es (eval env)
    Right (VListLit Nothing vs)
  eval env (EListLit (Just ty) es) = do
    ty' <- eval env ty
    vs <- mapListEither es (eval env)
    Right (VListLit (Just ty') vs)
  eval env (EListAppend x y) = do
    x' <- eval env x
    y' <- eval env y
    doListAppend x' y'
  eval env (ENaturalIsZero x)
    = do x' <- eval env x
         doNaturalIsZero x'
  eval env (EEmbed (Raw x)) = Left (ErrorMessage "Can't eval unresolved import")
  eval env (EEmbed (Resolved x)) = eval initEnv x

  partial
  doApply : Value -> Value -> Either Error Value
  doApply (VLambda ty closure) arg =
    evalClosure closure arg
  doApply (VNeutral (VPi dom ran) neu) arg =
    do arg' <- evalClosure ran arg
       Right (VNeutral arg' (NApp neu (Normal' dom arg)))
  doApply _ _ = Left EvalApplyErr

  partial
  doNaturalIsZero : Value -> Either Error Value
  doNaturalIsZero (VNaturalLit k) = Right (VBoolLit (k == 0))
  doNaturalIsZero (VNeutral VNatural neu) = Right (VNeutral VBool (NNaturalIsZero neu))
  doNaturalIsZero x = Left (EvalNaturalIsZeroErr (show x))

  doBoolAnd : Value -> Value -> Either Error Value
  doBoolAnd (VBoolLit x) (VBoolLit y) = Right (VBoolLit (x && y))
  doBoolAnd (VNeutral VBool v) y = Right (VNeutral VBool (NBoolAnd v (Normal' VBool y)))
  doBoolAnd _ _ = Left EvalBoolAndErr

  doAssert : Value -> Either Error Value
  doAssert v@(VEquivalent x y) = do
    xRb <- readBackTyped initCtx (VConst CType) x
    yRb <- readBackTyped initCtx (VConst CType) y
    case aEquiv xRb yRb of
         False => Left (AssertError ("Assert error: " ++ show x))
         True => Right (VAssert v)
  doAssert (VNeutral (VEquivalent x y) v)
    = Right (VNeutral (VEquivalent x y) (NAssert v))
  doAssert x = Left (AssertError ("Assert error: " ++ show x))

  doListAppend : Value -> Value -> Either Error Value
  doListAppend (VListLit x xs) (VListLit _ ys) =
    Right (VListLit x (xs ++ ys)) -- TODO dropping type info
  doListAppend (VNeutral (VList x) v) y =
    Right (VNeutral (VList x) (NListAppend v (Normal' (VList x) y)))
  doListAppend x y = Left (ListAppendError (show x ++ " " ++ show y))

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
  readBackNeutral : Ctx -> Neutral -> Either Error (Expr Void)
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
  readBackNeutral ctx (NEquivalent x y) = do
    x' <- readBackNeutral ctx x
    y' <- readBackNormal ctx y
    Right (EEquivalent x' y')
  readBackNeutral ctx (NAssert x) = do
    x' <- readBackNeutral ctx x
    Right (EAssert x')
  readBackNeutral ctx (NList a) = do
    a' <- readBackNeutral ctx a
    Right (EList a')
  readBackNeutral ctx (NListAppend x y) = do
    x' <- readBackNeutral ctx x
    y' <- readBackNormal ctx y
    Right (EListAppend x' y')

  readBackTyped : Ctx -> Ty -> Value -> Either Error (Expr Void)
  readBackTyped ctx (VPi dom ran) fun =
    let x = freshen (ctxNames ctx) (closureName ran)
        xVal = VNeutral dom (NVar x)
        ctx' = extendCtx ctx x dom in
    do ty' <- evalClosure ran xVal
       v' <- doApply fun xVal
       body <- readBackTyped ctx' ty' v'
       eTy <- readBackTyped ctx' (VConst CType) ty' -- TODO check this
       Right (ELam x eTy body)
  readBackTyped ctx ty (VEquivalent x y) = do -- TODO not sure is `ty` correct
    x' <- readBackTyped ctx ty x
    y' <- readBackTyped ctx ty y
    Right (EEquivalent x' y')
  readBackTyped ctx (VConst CType) (VAssert x) = do -- TODO not sure is `VConst CType` correct
    x' <- readBackTyped ctx (VConst CType) x
    Right (EAssert x')
  readBackTyped ctx (VConst x) (VConst y) = Right (EConst y) -- TODO check this
  readBackTyped ctx (VConst CType) VBool = Right EBool
  readBackTyped ctx (VConst CType) VNatural = Right ENatural
  readBackTyped ctx VBool (VBoolLit x) = Right (EBoolLit x)
  readBackTyped ctx VNatural (VNaturalLit x) = Right (ENaturalLit x)
  readBackTyped ctx t (VNeutral x z) = readBackNeutral ctx z
  readBackTyped ctx (VConst CType) (VPi aT bT) =
    let x = freshen (ctxNames ctx) (closureName bT) in
    do a <- readBackTyped ctx (VConst CType) aT
       b' <- evalClosure bT (VNeutral aT (NVar x))
       b <- readBackTyped (extendCtx ctx x aT) (VConst CType) b'
       Right (EPi x a b)
  readBackTyped ctx (VConst CType) (VList a) = do
    a' <- readBackTyped ctx (VConst CType) a
    Right (EList a')
  readBackTyped ctx (VList a) (VListLit Nothing vs) = do
    a' <- readBackTyped ctx (VConst CType) a
    es <- mapListEither vs (readBackTyped ctx a)
    Right (EListLit (Just a') es)
  readBackTyped ctx (VList a) (VListLit (Just ty) vs) = do
    a' <- readBackTyped ctx (VConst CType) a
    es <- mapListEither vs (readBackTyped ctx ty)
    -- TODO check if a=ty?
    Right (EListLit (Just a') es)
  readBackTyped _ t v = Left (ReadBackError ("error reading back: " ++ (show v) ++ " of type: " ++ (show v)))

  export
  partial
  readBackNormal : Ctx -> Normal -> Either Error (Expr Void)
  readBackNormal ctx (Normal' t v) = readBackTyped ctx t v

-- helpers
unexpected : Ctx -> String -> Value -> Either Error a
unexpected ctx str v = Left (Unexpected str v)

isPi : Ctx -> Value -> Either Error (Ty, Closure)
isPi _ (VPi a b) = Right (a, b)
isPi ctx other = unexpected ctx "Not a Pi type" other

isNat : Ctx -> Value -> Either Error ()
isNat _ VNatural = Right ()
isNat ctx other = unexpected ctx "Not Natural" other

isBool : Ctx -> Value -> Either Error ()
isBool _ VBool = Right ()
isBool ctx other = unexpected ctx "Not Bool" other

isList : Ctx -> Value -> Either Error ()
isList ctx (VList x) = Right ()
isList ctx other = unexpected ctx "Not List" other

isEquivalent : Ctx -> Value -> Either Error (Value, Value)
isEquivalent ctx (VEquivalent x y) = Right (x, y)
isEquivalent ctx other = unexpected ctx "Not Equivalent" other

isTerm : Ctx -> Value -> Either Error ()
isTerm _ (VPi _ _) = Right ()
isTerm _ (VBool) = Right ()
isTerm _ (VNatural) = Right ()
isTerm _ (VList _) = Right ()
isTerm ctx (VNeutral x _) = isTerm ctx x
isTerm ctx other = unexpected ctx "Not a term" other

isTypeKindSort : Ctx -> Value -> Either Error () -- TODO somehow generalise this an isTerm
isTypeKindSort _ (VConst CType) = Right ()
isTypeKindSort _ (VConst Kind) = Right ()
isTypeKindSort _ (VConst Sort) = Right ()
isTypeKindSort ctx (VNeutral x _) = isTypeKindSort ctx x
isTypeKindSort ctx other = unexpected ctx "Not type/kind/sort" other

lookupType : Ctx -> Name -> Either Error Ty -- didn't use message type
lookupType [] x = Left (ErrorMessage ("unbound variable: " ++ x))
lookupType ((y, e) :: ctx) x =
  (case x == y of
        False => lookupType ctx x
        True => (case e of
                      (Def t _) => Right t
                      (IsA t) => Right t))

axioms : (x : U) -> Either Error Value
axioms CType = Right (VConst Kind)
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
            else Left (ErrorMessage ("not alpha equivalent: " ++ show e1 ++ " : " ++ show e2))

  export
  partial
  check : Ctx -> Expr Void -> Ty -> Either Error ()
  check ctx (EConst CType) (VConst Kind) = Right ()
  check ctx (EConst Kind) (VConst Sort) = Right ()
  check ctx (EConst Sort) (VConst Sort) = Left SortError -- TODO check what happens here
  check ctx (ELam x ty body) t
    = do (a,b) <- isPi ctx t
         -- check ctx ty a TODO use ty?
         xV <- evalClosure b (VNeutral a (NVar x))
         check (extendCtx ctx x a) body xV
  check ctx (EAnnot x y) t
    = do xV <- synth ctx x
         yV <- eval (mkEnv ctx) y
         x' <- readBackTyped ctx xV (VConst CType)
         check ctx x' yV
         check ctx x' t -- TODO double check it makes sense to type check an annotation
  check ctx (EEquivalent x y) (VConst CType) = do
    xV <- eval (mkEnv ctx) x
    yV <- eval (mkEnv ctx) y
    xTy <- synth ctx x
    isTerm ctx xTy
    check ctx y xTy
  check ctx (EAssert a@(EEquivalent z w)) b@(VEquivalent x y) = do
    aTy <- synth ctx z
    aV <- eval (mkEnv ctx) a
    convert ctx aTy aV b
  check ctx (EBoolLit x) t = isBool ctx t
  check ctx (ENaturalLit k) t = isNat ctx t
  check ctx (EListLit Nothing xs) (VList a) = do
    mapListEither xs (\e => check ctx e a)
    Right ()
  check ctx (EListLit (Just x) xs) ty@(VList a) = do
    xV <- eval (mkEnv ctx) x
    convert ctx (VConst CType) xV ty
    mapListEither xs (\e => check ctx e a)
    Right ()
  check ctx other t
    = do t' <- synth ctx other
         convert ctx (VConst CType) t' t

  export
  synth : Ctx -> Expr Void -> Either Error Ty
  synth ctx (EVar x) = lookupType ctx x
  synth ctx (EConst x) = axioms x
  synth ctx (EPi x y z)
    = do yTy <- synth ctx y
         isTypeKindSort ctx yTy
         yV <- eval (mkEnv ctx) y
         zV <- eval (mkEnv (extendCtx ctx x yV)) z
         zTy <- synth (extendCtx ctx x yV) z
         isTypeKindSort ctx zTy
         case (yTy, zTy) of -- Feels like a hack. For test `FunctionTypeKindTypeA.dhall`
              (VConst Sort, VConst Kind) => Right (VConst Sort)
              _ => Right zTy
  synth ctx (ELam x ty b)
    = do xTy <- eval (mkEnv ctx) ty
         bTy <- synth (extendCtx ctx x xTy) b
         tyRb <- readBackTyped ctx (VConst CType) xTy
         bRb <- readBackTyped ctx (VConst CType) bTy
         Right (VPi xTy (MkClosure (mkEnv ctx) x tyRb bRb))
  synth ctx (EApp rator rand)
    = do funTy <- synth ctx rator
         (a, b) <- isPi ctx funTy
         check ctx rand a
         rand' <- eval (mkEnv ctx) rand
         evalClosure b rand'
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
  synth ctx e@(EEquivalent x y) = do
    check ctx e (VConst CType)
    Right (VConst CType)
  synth ctx (EAssert (EEquivalent x y)) = do
    xTy <- synth ctx x
    x' <- eval (mkEnv ctx) x
    y' <- eval (mkEnv ctx) y
    xRb <- readBackTyped ctx xTy x'
    yRb <- readBackTyped ctx xTy y'
    case aEquiv xRb yRb of -- TODO should eventually use CBOR to check
          False => Left (AssertError ("Not equivalent: " ++ show x ++ " : " ++ show y ++ ")"))
          True => Right (VEquivalent x' y')
  synth ctx (EList x) = do
    check ctx x (VConst CType)
    Right (VConst CType)
  synth ctx (EListLit Nothing []) = do
    Left (ErrorMessage ("Empty list needs a type"))
  synth ctx (EListLit Nothing (x :: xs)) = do
    ty <- synth ctx x
    readBackTyped ctx (VConst CType) ty
    mapListEither xs (\e => check ctx e ty)
    Right (VList ty)
  synth ctx (EListLit (Just ty) []) = do
    check ctx ty (VConst CType)
    ty' <- eval (mkEnv ctx) ty
    isList ctx ty'
    Right (ty')
  synth ctx (EListLit (Just ty) (x :: xs)) = do
    tyV <- eval (mkEnv ctx) ty
    isList ctx tyV
    xTy <- synth ctx x
    convert ctx (VConst CType) tyV xTy
    mapListEither xs (\e => check ctx e xTy)
    Right (xTy)
  synth ctx (EAssert other) = Left (AssertError ("Can't assert for expr: " ++ show other))
  synth ctx (EListAppend x y) = do
    xTy <- synth ctx x
    yTy <- synth ctx y
    isList ctx xTy
    convert ctx (VConst CType) xTy yTy
    Right (xTy)
  synth ctx (EEmbed (Raw _)) = Left (ErrorMessage "Can't synth unresolved import")
  synth ctx (EEmbed (Resolved x)) = synth initCtx x
