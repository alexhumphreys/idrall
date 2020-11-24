module Idrall.Check

import Idrall.Expr
import Idrall.Error
import Idrall.Value
import Idrall.Map

import Data.List

-- alpha equivalence
nestError : Either Error b -> Error -> Either Error b
nestError x e =
  case x of
       (Left e') => Left $ NestedError e e'
       (Right x') => Right x'

aEquivErr : (Show x) => x -> x -> Error
aEquivErr x y = AlphaEquivError $ show x ++ "\n not alpha equivalent to:\n" ++ show y

boolAEquiv : (Eq x, Show x) => x -> x -> Either Error ()
boolAEquiv a b =
  case a == b of
       True => Right ()
       False => Left $ aEquivErr a b

mutual
  aEquivHelper : (i : Integer) ->
                 Namespace -> Expr Void ->
                 Namespace -> Expr Void ->
                 Either Error ()
  aEquivHelper i ns1 (EVar x) ns2 (EVar y) =
    case (lookup x ns1, lookup y ns2) of
         (Nothing, Nothing) => boolAEquiv x y
         (Just j, Just k) => boolAEquiv j k
         (Just j, Nothing) => Left $ AlphaEquivError $ show j ++ " not found"
         (Nothing, Just k) => Left $ AlphaEquivError $ show k ++  " not found"
  aEquivHelper i ns1 (EPi x a1 r1) ns2 (EPi y a2 r2) = do
    aEquivHelper i ns1 a1 ns2 a2
    aEquivHelper (i+1) ((x, i) :: ns1) r1 ((y, i) :: ns2) r2
  aEquivHelper i ns1 (ELam x ty1 body1) ns2 (ELam y ty2 body2)
    = let newNs1 = (x, i) :: ns1
          newNs2 = (y, i) :: ns2 in do
      aEquivHelper i ns1 ty1 ns2 ty2
      aEquivHelper (i+1) newNs1 body1 newNs2 body2
  aEquivHelper i ns1 (EApp rator1 rand1) ns2 (EApp rator2 rand2) = do
    aEquivHelper i ns1 rator1 ns2 rator2
    aEquivHelper i ns1 rand1 ns2 rand2
  aEquivHelper i ns1 (ELet x1 t1 r1 e1) ns2 (ELet x2 t2 r2 e2)
    = let newNs1 = (x1, i) :: ns1
          newNs2 = (x2, i) :: ns2 in do
      aEquivMaybe i ns1 t1 ns2 t2 -- TODO not sure the type annotations matter for aEquiv-ness
      aEquivHelper i ns1 r1 ns2 r2
      aEquivHelper i newNs1 e1 newNs2 e2 -- TODO double check this, might need (i+1)
  aEquivHelper i ns1 (EAnnot w x) ns2 (EAnnot y z) = do
    aEquivHelper i ns1 w ns2 y
    aEquivHelper i ns1 x ns2 z
  aEquivHelper _ _ EBool _ EBool = Right ()
  aEquivHelper i ns1 (EBoolLit x) ns2 (EBoolLit y) = boolAEquiv x y
  aEquivHelper i ns1 (EBoolAnd w x) ns2 (EBoolAnd y z) = do
    aEquivHelper i ns1 w ns2 y
    aEquivHelper i ns1 x ns2 z
  aEquivHelper _ _ ENatural _ ENatural = Right ()
  aEquivHelper _ _ EInteger _ EInteger = Right ()
  aEquivHelper i ns1 (EIntegerLit x) ns2 (EIntegerLit y) = boolAEquiv x y
  aEquivHelper i ns1 (EIntegerNegate x) ns2 (EIntegerNegate y) =
    aEquivHelper i ns1 x ns2 y
  aEquivHelper _ _ (EConst x) _ (EConst y) = boolAEquiv x y
  aEquivHelper i ns1 (ENaturalLit x) ns2 (ENaturalLit y) = boolAEquiv x y
  aEquivHelper i ns1 (ENaturalIsZero x) ns2 (ENaturalIsZero y) =
    aEquivHelper i ns1 x ns2 y
  aEquivHelper _ _ EDouble _ EDouble = Right ()
  aEquivHelper i _ (EDoubleLit x) _ (EDoubleLit y) = boolAEquiv x y
  aEquivHelper i ns1 (EEquivalent w x) ns2 (EEquivalent y z) = do
    -- TODO should use CBOR encoding eventually
    aEquivHelper i ns1 w ns1 x
    aEquivHelper i ns1 w ns2 y
    aEquivHelper i ns2 y ns2 z
  aEquivHelper i ns1 (EAssert x) ns2 (EAssert y) =
    aEquivHelper i ns1 x ns2 y
  aEquivHelper i ns1 (EList x) ns2 (EList y) =
    aEquivHelper i ns1 x ns2 y
  aEquivHelper i ns1 (EListLit tx xs) ns2 (EListLit ty ys) = do
    aEquivMaybe i ns1 tx ns2 ty
    aEquivList i ns1 xs ns2 ys
  aEquivHelper i ns1 (EListAppend w x) ns2 (EListAppend y z) = do
    aEquivHelper i ns1 w ns2 y
    aEquivHelper i ns1 x ns2 z
  aEquivHelper i ns1 (EListHead w x) ns2 (EListHead y z) = do
    aEquivHelper i ns1 w ns2 y
    aEquivHelper i ns1 x ns2 z
  aEquivHelper i _ EListFold _ EListFold = Right ()
  aEquivHelper _ _ EText _ EText = Right ()
  aEquivHelper i ns1 (ETextLit a@(MkChunks xys z)) ns2 (ETextLit b@(MkChunks xys' z')) =
    -- TODO Not confindent that this is correct for all cases
    case (stringFromETextLit xys, stringFromETextLit xys') of
         (Just a, Just b) =>
            let l = a ++ z
                r = b ++ z' in
                boolAEquiv l r
         _ => aEquivTextLit i ns1 a ns2 b
  aEquivHelper i ns1 (EOptional x) ns2 (EOptional y) =
    aEquivHelper i ns1 x ns2 y
  aEquivHelper i ns1 (ENone x) ns2 (ENone y) =
    aEquivHelper i ns1 x ns2 y
  aEquivHelper i ns1 (ESome x) ns2 (ESome y) =
    aEquivHelper i ns1 x ns2 y
  aEquivHelper i ns1 (ERecord x) ns2 (ERecord y) =
    let xs = toList x
        ys = toList y in
    aEquivRecord i ns1 xs ns2 ys
  aEquivHelper i ns1 (ERecordLit x) ns2 (ERecordLit y) =
    let xs = toList x
        ys = toList y in
    aEquivRecord i ns1 xs ns2 ys
  aEquivHelper i ns1 (ECombine w x) ns2 (ECombine y z) = do
    aEquivHelper i ns1 w ns2 y
    aEquivHelper i ns1 x ns2 z
  aEquivHelper i ns1 (ECombineTypes w x) ns2 (ECombineTypes y z) = do
    aEquivHelper i ns1 w ns2 y
    aEquivHelper i ns1 x ns2 z
  aEquivHelper i ns1 (EUnion x) ns2 (EUnion y) =
    let xs = toList x
        ys = toList y in
    aEquivUnion i ns1 xs ns2 ys
  aEquivHelper i ns1 (EField x k) ns2 (EField y j) = do
    aEquivHelper i ns1 x ns2 y
    boolAEquiv k j
  aEquivHelper _ _ x _ y = Left $ aEquivErr x y

  aEquivMaybe : (i : Integer) ->
                Namespace -> Maybe (Expr Void) ->
                Namespace -> Maybe (Expr Void) -> Either Error ()
  aEquivMaybe i ns1 (Just a) ns2 (Just b) = aEquivHelper i ns1 a ns2 b
  aEquivMaybe _ _ Nothing _ Nothing = Right ()
  aEquivMaybe _ _ x _ y = Left $ aEquivErr x y

  aEquivList : (i : Integer) ->
               Namespace -> List (Expr Void) ->
               Namespace -> List (Expr Void) -> Either Error ()
  aEquivList i ns1 [] ns2 [] = Right ()
  aEquivList i ns1 (x :: xs) ns2 (y :: ys) = do
    aEquivHelper i ns1 x ns2 y
    aEquivList i ns1 xs ns2 ys
  aEquivList _ _ x _ y = Left $ aEquivErr x y

  aEquivRecord : (i : Integer) ->
                Namespace -> List (FieldName, Expr Void) ->
                Namespace -> List (FieldName, Expr Void) -> Either Error ()
  aEquivRecord i ns1 [] ns2 [] = Right ()
  aEquivRecord i ns1 ((k, v) :: xs) ns2 ((k', v') :: ys) = do
    aEquivHelper i ns1 v ns2 v'
    aEquivRecord i ns1 xs ns2 ys
    boolAEquiv k k'
  aEquivRecord _ _ x _ y = Left $ aEquivErr x y

  aEquivUnion : (i : Integer) ->
                Namespace -> List (FieldName, (Maybe (Expr Void))) ->
                Namespace -> List (FieldName, (Maybe (Expr Void))) -> Either Error ()
  aEquivUnion i ns1 [] ns2 [] = Right ()
  aEquivUnion i ns1 ((k, Nothing) :: xs) ns2 ((k', Nothing) :: ys) = do
    boolAEquiv k k'
    aEquivUnion i ns1 xs ns2 ys
  aEquivUnion i ns1 ((k, Just v) :: xs) ns2 ((k', Just v') :: ys) = do
    boolAEquiv k k'
    aEquivHelper i ns1 v ns2 v'
    aEquivUnion i ns1 xs ns2 ys
  aEquivUnion _ _ x _ y = Left $ aEquivErr x y

  aEquivTextLit : (i : Integer) ->
                  Namespace -> Chunks Void ->
                  Namespace -> Chunks Void -> Either Error ()
  aEquivTextLit i ns1 (MkChunks [] x) ns2 (MkChunks [] y) = boolAEquiv x y
  aEquivTextLit i ns1 (MkChunks xs x) ns2 (MkChunks ys y) =
    let xexprs = map snd xs
        yexprs = map snd ys
        exprsRes = aEquivList i ns1 xexprs ns2 yexprs
        strx = map fst xs
        stry = map fst ys
        strsRes = strx == stry
        in do
    boolAEquiv x y
    boolAEquiv strx stry
    exprsRes

  stringFromETextLit : List (String, Expr Void) -> Maybe String
  stringFromETextLit [] = Just neutral
  stringFromETextLit ((a, ETextLit (MkChunks xys z)) :: xs) = do
    rest <- stringFromETextLit xs
    mid <- stringFromETextLit xys
    Just (a ++ mid ++ z ++ rest)
  stringFromETextLit ((a, _) :: xs) = Nothing

aEquiv : Expr Void -> Expr Void -> Either Error ()
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
  covering
  evalClosure : Closure -> Value -> Either Error Value
  evalClosure (MkClosure env x ty e) v
    -- TODO not using this type info, Andras doesn't even store type
    -- info as part of Closure
    = do ty' <- eval env ty
         eval (extendEnv env x v) e

  evalVar : Env -> Name -> Either Error Value
  evalVar [] x = Left (MissingVar (x ++ " not found in env"))
  evalVar ((y, v) :: env) x
    = case x == y of
           True => Right v
           False => evalVar env x

  export
  covering
  eval : Env -> Expr Void -> Either Error Value
  eval env (EConst x) = Right (VConst x)
  eval env (EVar x)
    = evalVar env x
  eval env (EPi x dom ran)
    = do ty <- eval env dom
         Right (VPi ty (MkClosure env x dom ran))
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
                            eval (extendEnv env x vr) e
  eval env (EAnnot x _)
    = do x' <- eval env x
         Right x'
  eval env EBool = Right VBool
  eval env (EBoolLit x) = Right (VBoolLit x)
  eval env (EBoolAnd x y)
    = do x' <- eval env x
         y' <- eval env y
         doBoolAnd x' y'
  eval env EInteger = Right VInteger
  eval env (EIntegerLit k) = Right (VIntegerLit k)
  eval env (EIntegerNegate x)
    = do x' <- eval env x
         doIntegerNegate x'
  eval env ENatural = Right VNatural
  eval env (ENaturalLit k) = Right (VNaturalLit k)
  eval env EDouble = Right VDouble
  eval env (EDoubleLit k) = Right (VDoubleLit k)
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
  eval env (EListHead x y) = do
    x' <- eval env x
    y' <- eval env y
    doListHead x' y'
  eval env EListFold =
    Right $ VPrim $
      \a => Right $ VPrim $
        \c => case c of
                   (VListLit _ as) =>
                     Right $ VHLam (Typed "list" vType) $ \list =>
                     Right $ VHLam (Typed "cons" (vFun a $ vFun list list) ) $ \cons =>
                     Right $ VHLam (Typed "nil"  list) $ \nil =>
                       foldlM (\x,b => (vApp !(vApp cons x) b)) nil as
                   as => Right $ VHLam (ListFoldCl as) $
                        \t => Right $ VPrim $
                        \c => Right $ VPrim $
                        \n => Right $ VListFold a as t c n
    where
      foldlM : (Monad m, Traversable t) => (v -> v -> m v) -> v -> t v -> m v
      foldlM f x ys = foldl (\a,b => f !a b) (pure x) ys
  eval env EText = Right VText
  eval env (ETextLit (MkChunks xs x)) = do
    xs' <- traverse (mapChunks (eval env)) xs
    Right (VTextLit (MkVChunks xs' x))
  eval env (ENaturalIsZero x)
    = do x' <- eval env x
         doNaturalIsZero x'
  eval env (EOptional a) = Right (VOptional !(eval env a))
  eval env (ENone a) = Right (VNone !(eval env a))
  eval env (ESome a) = Right (VSome !(eval env a))
  eval env (ERecord x) =
    let xs = toList x in
    do xs' <- traverse (mapRecord (eval env)) xs
       Right (VRecord (fromList xs'))
  eval env (ERecordLit x) =
    let xs = toList x in
    do xs' <- traverse (mapRecord (eval env)) xs
       Right (VRecordLit (fromList xs'))
  eval env (ECombine x y) = do
    x' <- eval env x
    y' <- eval env y
    doCombine x' y'
  eval env (ECombineTypes x y) = do
    x' <- eval env x
    y' <- eval env y
    doCombine x' y'
  eval env (EUnion x) =
    let xs = toList x in
    do xs' <- traverse (mapUnion (eval env)) xs
       Right (VUnion (fromList xs'))
  eval env (EField (EUnion x) k) =
    let xs = toList x in do
      x' <- traverse (mapUnion (eval env)) xs
      case lookup k x' of
           Nothing => Left (FieldNotFoundError "k")
           (Just Nothing) => Right (VInject (fromList x') k Nothing)
           (Just (Just _)) => Right (VPrim $ \u => Right $ VInject (fromList x') k (Just u))
  eval env (EField x k) = Left (InvalidFieldType (show x))
  eval env (EEmbed (Raw x)) = absurd x
  eval env (EEmbed (Resolved x)) = eval initEnv x

  covering
  doApply : Value -> Value -> Either Error Value
  doApply (VLambda ty closure) arg =
    evalClosure closure arg
  doApply (VHLam i f) arg = (f arg)
  doApply (VNeutral (VPi dom ran) neu) arg =
    do arg' <- evalClosure ran arg
       Right (VNeutral arg' (NApp neu (Normal' dom arg)))
  doApply _ _ = Left EvalApplyErr

  doIntegerNegate : Value -> Either Error Value
  doIntegerNegate (VIntegerLit x) = Right (VIntegerLit (x*(-1)))
  doIntegerNegate (VNeutral VInteger neu) = Right (VNeutral VInteger (NIntegerNegate neu))
  doIntegerNegate x = Left (EvalIntegerNegateErr (show x))

  doNaturalIsZero : Value -> Either Error Value
  doNaturalIsZero (VNaturalLit k) = Right (VBoolLit (k == 0))
  doNaturalIsZero (VNeutral VNatural neu) = Right (VNeutral VBool (NNaturalIsZero neu))
  doNaturalIsZero x = Left (EvalNaturalIsZeroErr (show x))

  doBoolAnd : Value -> Value -> Either Error Value
  doBoolAnd (VBoolLit x) (VBoolLit y) = Right (VBoolLit (x && y))
  doBoolAnd (VNeutral VBool v) y = Right (VNeutral VBool (NBoolAnd v (Normal' VBool y)))
  doBoolAnd _ _ = Left EvalBoolAndErr

  covering
  doAssert : Value -> Either Error Value
  doAssert v@(VEquivalent x y) = do
    -- TODO VConst CType here fails for `assert : "foo${"1"}" === "foo1"`
    -- as it would need to read back as VText
    xRb <- readBackTyped initCtx (VConst CType) x
    yRb <- readBackTyped initCtx (VConst CType) y
    case aEquiv xRb yRb of
         Left _ => Left (AssertError (show xRb ++ " not equivalent to " ++ show yRb))
         Right _ => Right (VAssert v)
  doAssert (VNeutral (VEquivalent x y) v)
    = Right (VNeutral (VEquivalent x y) (NAssert v))
  doAssert x = Left (AssertError ("not an equivalence type: " ++ show x))

  doListAppend : Value -> Value -> Either Error Value
  doListAppend (VListLit x xs) (VListLit _ ys) =
    Right (VListLit x (xs ++ ys)) -- TODO dropping type info
  doListAppend (VNeutral (VList x) v) y =
    Right (VNeutral (VList x) (NListAppend v (Normal' (VList x) y)))
  doListAppend x y = Left (ListAppendError (show x ++ " " ++ show y))

  doListHead' : Value -> List Value -> Either Error Value
  doListHead' ty [] = Right (VNone ty)
  doListHead' ty (v :: vs) = Right (VSome v)

  doListHead : Value -> Value -> Either Error Value -- TODO dry
  doListHead ty@(VPi x z) (VListLit _ ys) = doListHead' ty ys
  doListHead ty@(VEquivalent x z) (VListLit _ ys) = doListHead' ty ys
  doListHead ty@VBool (VListLit _ ys) = doListHead' ty ys
  doListHead ty@VNatural (VListLit _ ys) = doListHead' ty ys
  doListHead ty@(VList x) (VListLit _ ys) = doListHead' ty ys
  doListHead ty@(VListLit x xs) (VListLit _ ys) = doListHead' ty ys
  doListHead ty@(VOptional x) (VListLit _ ys) = doListHead' ty ys
  doListHead (VNeutral (VConst CType) v) y =
    Right (VNeutral (VConst CType) (NListHead v (Normal' (VList (VNeutral (VConst CType) v)) y))) -- TODO double check
  doListHead x y = Left (ListHeadError (show x ++ " " ++ show y))

  doCombine : Value -> Value -> Either Error Value
  doCombine (VRecordLit x) (VRecordLit y) =
    Right (VRecordLit $ !(mergeWithApp doCombine x y))
  doCombine (VRecord x) (VRecord y) =
    Right (VRecord $ !(mergeWithApp doCombine x y))
  doCombine (VNeutral (VRecord x) v) y =
    -- won't know type of y here, might need to remove some types from rbt
    -- TODO will use an empty list for now
    Right (VNeutral (VRecord x) (NCombine v (Normal' (VRecord (fromList [])) y)))
  doCombine (VNeutral (VConst x) v) y =
    -- TODO the type of VRecord can be Type/Kind/Sort, not sure what to do here
    Right (VNeutral (VConst x) (NCombineTypes v (Normal' (VConst x) y)))
  doCombine x y = Left $ CombineError $ show x ++ show y

  -- fresh names
  nextName : Name -> Name
  nextName x = x ++ "'"

  -- TODO could possibly fail for a list like [n', n'', n']
  freshen : List Name -> Name -> Name
  -- freshen _ "_" = "_" -- TODO dangerous?
  freshen [] n = n
  freshen xs n = case elem n xs of
                   False => n
                   True => freshen xs (nextName n)

  public export
  vApp : Value -> Value -> Either Error Value
  vApp (VLambda _ t) u = evalClosure t u
  vApp (VHLam _ t) u = t u
  vApp t u = Left $ ErrorMessage $ show t ++ " : " ++ show u

  qApp : Ctx -> Expr Void -> Value -> Either Error (Expr Void)
  qApp ctx t VPrimVar = Right t
  qApp ctx t u        = Right $ EApp t !(readBackTyped ctx vType u)

  -- reading back
  covering
  readBackNeutral : Ctx -> Neutral -> Either Error (Expr Void)
  readBackNeutral ctx (NVar x) = Right (EVar x)
  readBackNeutral ctx (NIntegerNegate x) = do
    x' <- readBackNeutral ctx x
    Right (EIntegerNegate x')
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
  readBackNeutral ctx (NListHead x y) = do
    x' <- readBackNeutral ctx x
    y' <- readBackNormal ctx y
    Right (EListHead x' y')
  readBackNeutral ctx (NOptional a) = do
    a' <- readBackNeutral ctx a
    Right (EOptional a')
  readBackNeutral ctx (NNone a) = do
    a' <- readBackNeutral ctx a
    Right (ENone a')
  readBackNeutral ctx (NSome a) = do
    a' <- readBackNeutral ctx a
    Right (ESome a')
  readBackNeutral ctx (NCombine x y) = do
    x' <- readBackNeutral ctx x
    y' <- readBackNormal ctx y
    Right (ECombine x' y')
  readBackNeutral ctx (NCombineTypes x y) = do
    x' <- readBackNeutral ctx x
    y' <- readBackNormal ctx y
    Right (ECombineTypes x' y')

  covering
  readBackTyped : Ctx -> Ty -> Value -> Either Error (Expr Void)
  readBackTyped ctx (VPi dom ran) fun =
    let x = freshen (ctxNames ctx) (closureName ran)
        xVal = VNeutral dom (NVar x)
        ctx' = extendCtx ctx x dom in
    do ty' <- evalClosure ran xVal
       v' <- doApply fun xVal
       body <- readBackTyped ctx' ty' v'
       eTy <- readBackTyped ctx (VConst CType) ty'
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
  readBackTyped ctx (VConst CType) VNatural = Right ENatural -- TODO do any of these need (VConst CType)?
  readBackTyped ctx (VConst CType) VInteger = Right EInteger
  readBackTyped ctx VBool (VBoolLit x) = Right (EBoolLit x)
  readBackTyped ctx VInteger (VIntegerLit x) = Right (EIntegerLit x)
  readBackTyped ctx VNatural (VNaturalLit x) = Right (ENaturalLit x)
  readBackTyped ctx (VConst CType) VDouble = Right EDouble
  readBackTyped ctx VDouble (VDoubleLit x) = Right (EDoubleLit x)
  readBackTyped ctx t (VNeutral x z) = readBackNeutral ctx z
  readBackTyped ctx (VConst CType) (VPi aT bT) =
    let x = freshen (ctxNames ctx) (closureName bT) in
    do a <- readBackTyped ctx (VConst CType) aT
       b' <- evalClosure bT (VNeutral aT (NVar x))
       b <- readBackTyped (extendCtx ctx x aT) (VConst CType) b'
       Right (EPi x a b)
  readBackTyped ctx (VConst CType) (VHPi i ty f) =
    let i' = freshen (ctxNames ctx) i in
    do a <- readBackTyped ctx (VConst CType) ty
       body' <- readBackTyped ctx (VConst CType) (f (VNeutral ty (NVar i')))
       -- CType is _probably_ fine here ^^^^^
       Right (EPi i' a body')
  readBackTyped ctx (VPi aT bT) (VHLam i f) =
    let x = freshen (ctxNames ctx) (closureName bT) in do
      b' <- evalClosure bT (VNeutral aT (NVar x))
      case i of
           Prim => readBackTyped ctx b' !(f VPrimVar) -- TODO double check b' here
           Typed str v => -- TODO not sure about this case, esp the vType and NVar parts
             Right $ ELam str
                          !(readBackTyped ctx vType v)
                          !(readBackTyped (extendCtx ctx str vType) vType !(f (VNeutral vType (NVar str))))
           ListFoldCl _ => readBackTyped ctx b' !(f VPrimVar)
  readBackTyped ctx (VConst CType) (VList a) = do
    a' <- readBackTyped ctx (VConst CType) a
    Right (EList a')
  readBackTyped ctx (VList a) (VListLit Nothing vs) = do
    a' <- readBackTyped ctx (VConst CType) a
    es <- mapListEither vs (readBackTyped ctx a)
    Right (EListLit (Just a') es)
  readBackTyped ctx (VList a) (VListLit (Just ty) vs) = do
    a' <- readBackTyped ctx (VConst CType) a
    es <- mapListEither vs (readBackTyped ctx a) -- Passing a here should confirm ty=a
    Right (EListLit (Just a') es)
  readBackTyped ctx _ (VListFold a l t u v) = do
    a' <- readBackTyped ctx (VConst CType) a
    l' <- readBackTyped ctx (VConst CType) l
    t' <- readBackTyped ctx (VConst CType) t
    u' <- readBackTyped ctx (VConst CType) u
    v' <- readBackTyped ctx (VConst CType) v
    Right $ (EApp (EApp (EApp (EApp (EApp EListFold a') l') t') u') v')
  readBackTyped ctx (VConst CType) VText = Right EText
  readBackTyped ctx VText (VTextLit (MkVChunks xs x)) =
    let f = mapChunks (readBackTyped ctx VText) in
    do
    xs' <- traverse f xs
    Right (ETextLit (MkChunks xs' x))
  readBackTyped ctx (VConst CType) (VOptional a) = do
    a' <- readBackTyped ctx (VConst CType) a
    Right (EOptional a')
  readBackTyped ctx (VOptional ty) (VNone ty') = do
    ety <- readBackTyped ctx (VConst CType) ty
    ety' <- readBackTyped ctx (VConst CType) ty'
    case aEquiv ety ety' of -- TODO should this check be happening here?
      Right _ => Right (ENone ety')
      Left _ => Left (ReadBackError ("error reading back None: " ++ (show ety) ++ " is not alpha equivalent to " ++ (show ety')))
  readBackTyped ctx (VOptional ty) (VSome a) = do
    a' <- readBackTyped ctx ty a
    Right (ESome a')
  readBackTyped ctx (VConst _) (VRecord a) = do
    a' <- traverse (mapRecord (readBackTyped ctx (VConst CType))) (toList a)
    Right (ERecord (fromList a'))
  readBackTyped ctx (VRecord a) (VRecordLit b) =
    let as = toList a
        bs = toList b in
    Right (ERecordLit (fromList !(readBackRecordLit ctx as bs)))
  readBackTyped ctx (VConst _) (VUnion a) = do
    a' <- traverse (readBackUnion ctx) (toList a)
    Right (EUnion (fromList a'))
  readBackTyped ctx (VUnion _) (VInject a k arg) =
    let kV = lookup k a in
    case (kV, arg) of
         (Just (Just k'), Just arg') =>
           do aRB <- traverse (readBackUnion ctx) (toList a)
              arg'' <- readBackTyped ctx k' arg'
              Right (EApp (EField (EUnion (fromList aRB)) k) (arg''))
         (Just Nothing, Just arg') => Left (FieldArgMismatchError ("No type for param " ++ show k))
         (Just _, _) => Right (EField
                                      (EUnion (fromList !(traverse (readBackUnion ctx) (toList a)))) k)
         (Nothing, _) => Left (FieldNotFoundError (show k))
  readBackTyped _ t v = Left (ReadBackError ("error reading back: " ++ (show v) ++ " of type: " ++ (show t)))

  readBackRecordLit : Ctx
                   -> List (FieldName, Value)
                   -> List (FieldName, Value)
                   -> Either Error (List (FieldName, (Expr Void)))
  readBackRecordLit ctx [] [] = Right []
  readBackRecordLit ctx ((k, v) :: xs) ((k', v') :: ys) =
    case k == k' of -- TODO may be unecessary, or could be done better
         False => Left (ReadBackError ("keys don't match: " ++ show k ++ " and " ++ show k'))
         True => do rest <- readBackRecordLit ctx xs ys
                    Right ((k, !(readBackTyped ctx v v')) :: rest)
  readBackRecordLit ctx _ _ = Left (ReadBackError ("wrong type for record: " ++ " ")) -- TODO improve this error

  readBackUnion : Ctx -> (FieldName, Maybe Value) -> Either Error (FieldName, Maybe (Expr Void))
  readBackUnion ctx (k, Nothing) = Right (k, Nothing)
  readBackUnion ctx (k, Just v) = Right (k, Just !(readBackTyped ctx (VConst CType) v))
    -- TODO is (VConst CType) always right here ^^^? Looks like rBT ignores the Ty param when reading back VConsts so maybe?

  covering
  export
  readBackNormal : Ctx -> Normal -> Either Error (Expr Void)
  readBackNormal ctx (Normal' t v) = readBackTyped ctx t v

-- helpers
unexpected : Ctx -> String -> Value -> Either Error a
unexpected ctx str v = Left (Unexpected $ str ++ " Value: " ++ show v)

isInteger : Ctx -> Value -> Either Error ()
isInteger _ VInteger = Right ()
isInteger ctx other = unexpected ctx "Not Integer" other

isNat : Ctx -> Value -> Either Error ()
isNat _ VNatural = Right ()
isNat ctx other = unexpected ctx "Not Natural" other

isDouble : Ctx -> Value -> Either Error ()
isDouble _ VDouble = Right ()
isDouble ctx other = unexpected ctx "Not Double" other

isBool : Ctx -> Value -> Either Error ()
isBool _ VBool = Right ()
isBool ctx other = unexpected ctx "Not Bool" other

isList : Ctx -> Value -> Either Error Ty -- TODO make return type more obvious
isList ctx (VList x) = Right x
isList ctx other = unexpected ctx "Not List" other

isText : Ctx -> Value -> Either Error ()
isText _ VText = Right ()
isText ctx other = unexpected ctx "Not Text" other

isRecord : Ctx -> Value -> Either Error (SortedMap FieldName Value)
isRecord _ (VRecord x) = Right x
isRecord ctx other = unexpected ctx "Not Record" other

isOptional : Ctx -> Value -> Either Error ()
isOptional ctx (VOptional x) = Right ()
isOptional ctx other = unexpected ctx "Not Optional" other

isEquivalent : Ctx -> Value -> Either Error (Value, Value)
isEquivalent ctx (VEquivalent x y) = Right (x, y)
isEquivalent ctx other = unexpected ctx "Not Equivalent" other

isTerm : Ctx -> Value -> Either Error ()
isTerm _ (VPi _ _) = Right ()
isTerm _ (VBool) = Right ()
isTerm _ (VNatural) = Right ()
isTerm _ (VInteger) = Right ()
isTerm _ (VDouble) = Right ()
isTerm _ (VList _) = Right ()
isTerm _ (VOptional _) = Right ()
isTerm ctx (VNeutral x _) = isTerm ctx x
isTerm ctx other = unexpected ctx "Not a term" other

isTypeKind : Ctx -> Value -> Either Error ()
isTypeKind _ (VConst CType) = Right ()
isTypeKind _ (VConst Kind) = Right ()
isTypeKind ctx (VNeutral x _) = isTypeKind ctx x
isTypeKind ctx other = unexpected ctx "Not a type or kind" other

isTermTypeKind : Ctx -> Value -> Either Error ()
isTermTypeKind _ (VPi _ _) = Right ()
isTermTypeKind _ (VBool) = Right ()
isTermTypeKind _ (VNatural) = Right ()
isTermTypeKind _ (VInteger) = Right ()
isTermTypeKind _ (VDouble) = Right ()
isTermTypeKind _ (VList _) = Right ()
isTermTypeKind _ (VOptional _) = Right ()
isTermTypeKind _ (VConst CType) = Right ()
isTermTypeKind _ (VConst Kind) = Right ()
isTermTypeKind ctx (VNeutral x _) = isTerm ctx x
isTermTypeKind ctx x = (isTypeKind ctx x)

isTypeKindSort : Ctx -> Value -> Either Error () -- TODO add Alternative Either
isTypeKindSort _ (VConst CType) = Right ()
isTypeKindSort _ (VConst Kind) = Right ()
isTypeKindSort _ (VConst Sort) = Right ()
isTypeKindSort ctx (VNeutral x _) = isTypeKindSort ctx x
isTypeKindSort ctx other = unexpected ctx "Not type/kind/sort" other

lookupType : Ctx -> Name -> Either Error Ty -- didn't use message type
lookupType [] x = Left (MissingVar x)
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
  export
  covering
  convert : Ctx -> Ty -> Value -> Value -> Either Error ()
  convert ctx t v1 v2
    = do e1 <- readBackTyped ctx t v1
         e2 <- readBackTyped ctx t v2
         case aEquiv e1 e2 of
            Right _ => Right ()
            Left y => Left (ErrorMessage ("not alpha equivalent: " ++ show e1 ++ " : " ++ show e2 ++ " ++++++++++" ++ show y))

  export
  covering
  check : Ctx -> Expr Void -> Ty -> Either Error ()
  check ctx (EConst CType) (VConst Kind) = Right ()
  check ctx (EConst Kind) (VConst Sort) = Right ()
  check ctx (EConst Sort) (VConst Sort) = Left SortError -- TODO check what happens here
  check ctx (ELam x ty body) (VPi a b)
    = do -- TODO use ty?
         xV <- evalClosure b (VNeutral a (NVar x))
         check (extendCtx ctx x a) body xV
  check ctx (ELam x ty body) (VHPi i ty' f) = do
    check (extendCtx ctx x ty') body (f ty')
  check ctx (ELam x ty body) other = unexpected ctx "Not a Pi type" other
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
  check ctx (EIntegerLit k) t = isInteger ctx t
  check ctx (ENaturalLit k) t = isNat ctx t
  check ctx (EDoubleLit k) t = isDouble ctx t
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

  listFoldTy : Value -> Value
  listFoldTy a =
    VHPi "list" vType $ \list =>
    VHPi "cons" (vFun (vFun a list) list) $ \cons =>
    VHPi "nil"  list $ \nil =>
    list

  export
  covering
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
         case funTy of
              (VPi a b) => do
                 check ctx rand a
                 rand' <- eval (mkEnv ctx) rand
                 evalClosure b rand'
              (VHPi i b f) => do
                 check ctx rand b
                 rand' <- eval (mkEnv ctx) rand
                 Right (f rand')
              other => unexpected ctx "Not a Pi type" other
  synth ctx (ELet x ann v e)
    = case ann of
           Nothing =>
              do xTy <- synth ctx v
                 synth (define ctx x xTy !(eval (mkEnv ctx) v)) e
           (Just ann') =>
              do check ctx ann' (VConst CType)
                 xTy <- eval (mkEnv ctx) ann'
                 check ctx v xTy
                 synth (define ctx x xTy !(eval (mkEnv ctx) v)) e
  synth ctx (EAnnot e t)
    = do tV <- eval (mkEnv ctx) t
         check ctx e tV
         Right tV
  synth ctx EBool = Right (VConst CType)
  synth ctx (EBoolLit x) = Right (VBool)
  synth ctx (EBoolAnd x y)
    = do check ctx x VBool
         check ctx y VBool
         Right (VBool)
  synth ctx EInteger = Right (VConst CType)
  synth ctx (EIntegerLit k) = Right (VInteger)
  synth ctx (EIntegerNegate x)
    = do check ctx x VInteger
         Right (VInteger)
  synth ctx ENatural = Right (VConst CType)
  synth ctx (ENaturalLit k) = Right (VNatural)
  synth ctx (ENaturalIsZero x)
    = do check ctx x VNatural
         Right (VBool)
  synth ctx EDouble = Right (VConst CType)
  synth ctx (EDoubleLit k) = Right (VDouble)
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
          Left _ => Left (AssertError ("Not equivalent: " ++ show x ++ " : " ++ show y ++ ")"))
          Right _ => Right (VEquivalent x' y')
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
  synth ctx (EListHead x y) = do
    xTy <- synth ctx x
    check ctx x (VConst CType)
    xVal <- eval (mkEnv ctx) x
    yTy <- synth ctx y
    check ctx y (VList xVal)
    ty <- isList ctx yTy
    Right (VOptional ty)
  synth ctx EListFold =
    Right $ VHPi "a" vType $ \a => vFun (VList a) (listFoldTy a)
  synth ctx EText = Right (VConst CType)
  synth ctx (ETextLit (MkChunks xs x)) =
    let go = mapChunks (\e => check ctx e VText) in do
    traverse go xs
    Right VText
  synth ctx (EOptional x) = do
    check ctx x (VConst CType)
    Right (VConst CType)
  synth ctx (ENone ty) = do
    check ctx ty (VConst CType)
    ty' <- eval (mkEnv ctx) ty
    Right (VOptional ty')
  synth ctx (ESome x) = do
    x' <- eval (mkEnv ctx) x
    xTy' <- synth ctx x
    isTerm ctx xTy'
    Right (VOptional xTy')
  synth ctx (ERecordLit x) =
    let xs = toList x in
    do xs' <- traverse (mapRecord (synth ctx)) xs
       Right (VRecord (fromList xs'))
  synth ctx (ERecord x) =
    let xs = toList x in -- TODO triple traverse here, might be slow
    do xs' <- traverse (mapRecord (synth ctx)) xs
       traverse (mapRecord (isTypeKindSort ctx)) xs'
       ty <- foldl getHighestType' (Right (VConst CType)) (map snd xs')
       Right ty
    where
      getHighestType' : (acc : Either Error Ty) -> Ty -> Either Error Ty -- TODO DRY with below
      getHighestType' e@(Left _) _ = e
      getHighestType' (Right (VConst CType)) (VConst Kind) = Right (VConst Kind)
      getHighestType' (Right _) (VConst Sort) = Right (VConst Sort)
      getHighestType' acc@(Right _) _ = acc -- relying on acc starting as (VConst CType)
  synth ctx (ECombine x y) = do
    xty <- synth ctx x
    yty <- synth ctx y
    xSm <- isRecord ctx xty
    ySm <- isRecord ctx yty
    Right $ VRecord !(mergeWithApp doCombine xSm ySm)
  synth ctx (ECombineTypes x y) = do
    xV <- eval (mkEnv ctx) x
    yV <- eval (mkEnv ctx) y
    xSm <- isRecord ctx xV
    ySm <- isRecord ctx yV
    combo <- (doCombine xV yV)
    rbCombo <- readBackTyped ctx (VConst CType) combo
    synth ctx rbCombo
  synth ctx (EUnion x) =
    let kvs = SortedMap.toList x in do -- TODO use SortedMap Traversable with idris2
      types <- traverse synthUnion kvs
      ty <- foldl getHighestType (Right (VConst CType)) (map snd types)
      Right ty
    where
      synthUnion : (FieldName, Maybe (Expr Void)) -> Either Error (FieldName, Maybe Ty)
      synthUnion (k, Nothing) = Right (k, Nothing)
      synthUnion (k, Just b) = do
        b' <- synth ctx b
        isTypeKindSort ctx b'
        Right (k, Just b')
      getHighestType : (acc : Either Error Ty) -> Maybe Ty -> Either Error Ty
      getHighestType e@(Left _) _ = e
      getHighestType (Right (VConst CType)) (Just (VConst Kind)) = Right (VConst Kind)
      getHighestType (Right _) (Just (VConst Sort)) = Right (VConst Sort)
      getHighestType acc@(Right _) _ = acc -- relying on acc starting as (VConst CType)
  synth ctx (EField u@(EUnion x) k) =
    let xs = toList x in do
      synth ctx u
      xs' <- traverse (mapUnion (eval (mkEnv ctx))) xs
      xsRb <- traverse (mapUnion (readBackTyped ctx (VConst CType))) xs'
      case lookup k xs' of
           Nothing => Left (FieldNotFoundError "k")
           (Just Nothing) => Right (VUnion (fromList xs'))
           (Just (Just x')) =>
              Right (vFun x' (VUnion (fromList xs')))
  synth ctx (EField x k) = Left (InvalidFieldType (show x))
  synth ctx (EEmbed (Raw x)) = absurd x
  synth ctx (EEmbed (Resolved x)) = synth initCtx x -- Using initCtx here to ensure fresh context.
