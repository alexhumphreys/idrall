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
  aEquivHelper i ns1 (EVar x w) ns2 (EVar y z) =
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
  aEquivHelper i ns1 EIntegerNegate ns2 EIntegerNegate = Right ()
  aEquivHelper _ _ (EConst x) _ (EConst y) = boolAEquiv x y
  aEquivHelper i ns1 (ENaturalLit x) ns2 (ENaturalLit y) = boolAEquiv x y
  aEquivHelper i ns1 ENaturalIsZero ns2 ENaturalIsZero = Right ()
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
  aEquivHelper i ns1 EListHead ns2 EListHead = Right ()
  aEquivHelper _ _ EText _ EText = Right ()
  aEquivHelper i ns1 (ETextLit a@(MkChunks xys z)) ns2 (ETextLit b@(MkChunks xys' z')) =
    -- TODO Not confindent that this is correct for all cases
    case (stringFromETextLit xys, stringFromETextLit xys') of
         (Just a, Just b) =>
            let l = a ++ z
                r = b ++ z' in
                boolAEquiv l r
         _ => aEquivTextLit i ns1 a ns2 b
  aEquivHelper i ns1 EOptional ns2 EOptional = Right ()
  aEquivHelper i ns1 (ESome x) ns2 (ESome y) =
    aEquivHelper i ns1 x ns2 y
  aEquivHelper i ns1 ENone ns2 ENone = Right ()
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

-- evaluator
mutual
  inst : Closure -> Value -> Either Error Value
  inst = evalClosure

  covering
  evalClosure : Closure -> Value -> Either Error Value
  evalClosure (MkClosure x env e) v
    = do eval (Extend env x v) e

  evalVar : Env' -> Name -> Int -> Either Error Value
  evalVar Empty x i = pure $ VVar x (0 - i - 1)
  evalVar (Skip env x') x i =
    case x == x' of
         True => if i == 0 then pure $ VVar x (countName x env) else evalVar env x (i - 1)
         False => evalVar env x i
  evalVar (Extend env x' v) x i =
    case x == x' of
         True => if i == 0 then pure v else evalVar env x (i - 1)
         False => evalVar env x i

  vVar : Env' -> Name -> Int -> Either Error Value
  vVar = evalVar

  export
  covering
  eval : Env' -> Expr Void -> Either Error Value
  eval env (EConst x) = Right (VConst x)
  eval env (EVar x i)
    = evalVar env x i
  eval env (ELam x ty body)
    = do vTy <- eval env ty
         Right (VLambda vTy (MkClosure x env body))
  eval env (EPi x dom ran)
    = do ty <- eval env dom
         Right (VPi ty (MkClosure x env ran))
  eval env (EApp rator rand)
    = do rator' <- eval env rator
         rand' <- eval env rand
         doApply rator' rand'
  eval env (ELet x _ r e) =
    do vr <- eval env r
       eval (Extend env x vr) e
  eval env (EAnnot x _) = eval env x
  eval env EBool = Right VBool
  eval env (EBoolLit x) = Right (VBoolLit x)
  eval env (EBoolAnd x y)
    = do x' <- eval env x
         y' <- eval env y
         case (x', y') of
              (VBoolLit True, u) => Right u
              (VBoolLit False, u) => Right $ VBoolLit False
              (t, VBoolLit True) => Right t
              (t, VBoolLit False) => Right $ VBoolLit False
              (t, u) => case conv env t u of
                             Right _ => Right t
                             Left _ => Right $ VBoolAnd t u -- TODO check this matches the | behaviour
  eval env ENatural = Right VNatural
  eval env (ENaturalLit k) = Right (VNaturalLit k)
  eval env ENaturalIsZero = Right $ VPrim $
                              \c => case c of
                                      VNaturalLit n => Right $ VBoolLit (n == 0)
                                      n             => Right $ VNaturalIsZero n
  eval env EInteger = Right VInteger
  eval env (EIntegerLit k) = Right (VIntegerLit k)
  eval env EIntegerNegate = Right $ VPrim $
                            \c => case c of
                                       VIntegerLit n => Right $ VIntegerLit (negate n)
                                       n             => Right $ VIntegerNegate n
  eval env EDouble = Right VDouble
  eval env (EDoubleLit k) = Right (VDoubleLit k)
  eval env EText = Right VText
  eval env (ETextLit (MkChunks xs x)) = do
    xs' <- traverse (mapChunks (eval env)) xs
    Right (VTextLit (MkVChunks xs' x))
  eval env EList = do
    Right $ VPrim $ \a => Right $ VList a
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
  eval env EListHead =
    Right $ VPrim $ \a =>
      Right $ VPrim $
             \c => case c of
                        VListLit _ [] => Right $ VNone a
                        VListLit _ (h :: _) => Right $ VSome h
                        as => Right $ VListHead a as
  eval env EOptional = Right $ VPrim $ \a => Right $ VOptional a
  eval env (ESome a) = Right (VSome !(eval env a))
  eval env ENone = Right $ VPrim $ \a => Right $ VNone a
  eval env (EEquivalent x y) =
    do xV <- eval env x
       yV <- eval env y
       Right (VEquivalent xV yV)
  eval env (EAssert x) = do
    xV <- eval env x
    doAssert env xV
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
  eval env (EEmbed (Resolved x)) = eval Empty x

  covering
  doApply : Value -> Value -> Either Error Value
  doApply (VLambda ty closure) arg =
    evalClosure closure arg
  doApply (VHLam i f) arg = (f arg)
  doApply f arg = Right $ VApp f arg

  vApp : Value -> Value -> Either Error Value
  vApp = doApply

  covering
  doAssert : Env' -> Value -> Either Error Value
  doAssert env v@(VEquivalent t u) = do
    conv env t u
    pure $ VAssert v
  doAssert env x = Left (AssertError ("not an equivalence type: " ++ show x))

  doListAppend : Value -> Value -> Either Error Value
  doListAppend (VListLit _ []) u = Right u
  doListAppend t (VListLit _ []) = Right t
  doListAppend (VListLit t xs) (VListLit _ ys) =
    Right (VListLit t (xs ++ ys))
  doListAppend x y = Right $ VListAppend x y

  doCombine : Value -> Value -> Either Error Value
  doCombine (VRecordLit x) (VRecordLit y) =
    Right (VRecordLit $ !(mergeWithApp doCombine x y))
  doCombine (VRecord x) (VRecord y) =
    Right (VRecord $ !(mergeWithApp doCombine x y))
  doCombine x y = Right $ VCombineTypes x y

  -- conversion checking
  -- Needs to be in mutual block with eval because it's used by Bool builtins

  countName : Name -> Env' -> Int
  countName x env = go 0 env
  where
    go : (acc : Int) -> Env' -> Int
    go acc Empty = acc
    go acc (Skip env x') = go (if x == x' then acc + 1 else acc) env
    go acc (Extend env x' _) = go (if x == x' then acc + 1 else acc) env

  convFresh : Name -> Env' -> (Name, Value)
  convFresh x env = (x, VVar x (countName x env))

  convFreshCl : Closure -> Env' -> (Name, Value, Closure)
  convFreshCl cl@(MkClosure x _ _) env = (x, snd (convFresh x env), cl)

  convErr : (Show x) => x -> x -> Error
  convErr x y = AlphaEquivError $ show x ++ "\n not alpha equivalent to:\n" ++ show y

  strFromChunks : List (String, Value) -> Maybe String
  strFromChunks [] = Just neutral
  strFromChunks ((str, (VTextLit (MkVChunks xys' y))) :: xs') = do
    rest <- strFromChunks xs'
    mid <- strFromChunks xys'
    Just (str ++ mid ++ y ++ rest)
  strFromChunks ((str, _) :: xs') = Nothing

  convChunks : Env' -> VChunks -> VChunks -> Either Error ()
  convChunks env (MkVChunks [] z) (MkVChunks [] z') = convEq z z'
  convChunks env (MkVChunks ((s, t) :: xys) z) (MkVChunks ((s', t') :: xys') z') = do
    convEq s s'
    conv env t t'
    convChunks env (MkVChunks xys z) (MkVChunks xys' z')
  convChunks env _ _ = ?convChunksErr

  convList : Env' -> List Value -> List Value -> Either Error ()
  convList env [] [] = pure ()
  convList env (t :: xs) (t' :: xs') = do
    conv env t t'
    convList env xs xs'
  convList env _ _ = ?convListErr

  convUnion : Env' -> List (FieldName, Maybe Value) -> List (FieldName, Maybe Value) -> Either Error ()
  convUnion env [] [] = pure ()
  convUnion env ((x, Just t) :: xs) ((x', Just t') :: ys) = do
    convEq x x'
    conv env t t'
    convUnion env xs ys
  convUnion env ((x, Nothing) :: xs) ((x', Nothing) :: ys) = do
    convEq x x'
    convUnion env xs ys
  convUnion env _ _ = ?convUnionErr

  convEq : (Eq x, Show x) => x -> x -> Either Error ()
  convEq a b =
    case a == b of
         True => Right ()
         False => Left $ aEquivErr a b

  convSkip : Env' -> Name -> Value -> Value -> Either Error ()
  convSkip env x = conv (Skip env x)

  conv : Env' -> Value -> Value -> Either Error ()
  conv env (VConst k) (VConst k') = convEq k k'
  conv env (VVar x i) (VVar x' i') = do
    convEq x x'
    convEq i i'

  conv env (VLambda _ t) (VLambda _ t') =
    let (x, v, t) = convFreshCl t env in do
    convSkip env x !(inst t v) !(inst t' v)
  conv env (VLambda _ t) (VHLam _ t') =
    let (x, v, t) = convFreshCl t env in do
    convSkip env x !(inst t v) !(t' v)
  conv env (VLambda _ t) t' =
    let (x, v, t) = convFreshCl t env in do
    convSkip env x !(inst t v) !(vApp t' v)
  conv env (VHLam _ t) (VLambda _ t') =
    let (x, v, t') = convFreshCl t' env in do
    convSkip env x !(t v) !(inst t' v)
  conv env (VHLam _ t) (VHLam _ t') =
    let (x, v) = convFresh "x" env in do
    convSkip env x !(t v) !(t' v)
  conv env (VHLam _ t) t' =
    let (x, v) = convFresh "x" env in do
    convSkip env x !(t v) !(vApp t' v)
  conv env t (VLambda _ t') =
    let (x, v, t') = convFreshCl t' env in do
    convSkip env x !(vApp t v) !(inst t' v)
  conv env t (VHLam _ t') =
    let (x, v) = convFresh "x" env in do
    convSkip env x !(vApp t v) !(t' v)

  conv env (VPi a b) (VPi a' b') =
    let (x, v, b') = convFreshCl b' env in do
    conv env a a'
    convSkip env x !(inst b v) !(inst b' v)
  conv env (VPi a b) (VHPi x a' b') =
    let (x, v) = convFresh "x" env in do
    conv env a a'
    convSkip env x !(inst b v) !(b' v)
  conv env (VHPi _ a b) (VPi a' b') =
    let (x, v, b') = convFreshCl b' env in do
    conv env a a'
    convSkip env x !(b v) !(inst b' v)
  conv env (VHPi _ a b) (VHPi x a' b') =
    let (x, v) = convFresh "x" env in do
    conv env a a'
    convSkip env x !(b v) !(b' v)

  conv env (VApp t u) (VApp t' u') = do
    conv env t t'
    conv env u u'
  conv env VBool VBool = pure ()
  conv env (VBoolLit b) (VBoolLit b') = convEq b b'
  conv env (VBoolAnd t u) (VBoolAnd t' u') = do
    conv env t t'
    conv env u u'
  conv env VNatural VNatural = pure ()
  conv env (VNaturalLit k) (VNaturalLit k') = convEq k k'
  conv env (VNaturalIsZero t) (VNaturalIsZero t') = conv env t t'
  conv env VInteger VInteger = pure ()
  conv env (VIntegerLit t) (VIntegerLit t') = convEq t t'
  conv env (VIntegerNegate t) (VIntegerNegate t') = conv env t t'
  conv env VDouble VDouble = pure ()
  conv env (VDoubleLit t) (VDoubleLit t') = convEq t t' -- TODO use binary encode
  conv env VText VText = pure ()
  conv env (VTextLit t@(MkVChunks xys z)) (VTextLit u@(MkVChunks xys' z')) =
    let l = strFromChunks xys
        r = strFromChunks xys' in
    case (l, r) of
         ((Just l'), (Just r')) => do
           convEq (l' ++ z) (r' ++ z')
         _ => convChunks env t u
  conv env (VList a) (VList a') = conv env a a'
  conv env (VListLit _ xs) (VListLit _ xs') = convList env xs xs'
  conv env (VListAppend t u) (VListAppend t' u') = do
    conv env t t'
    conv env u u'
  conv env (VListHead _ t) (VListHead _ t') = conv env t t'
  conv env (VOptional a) (VOptional a') = conv env a a'
  conv env (VNone _) (VNone _) = pure ()
  conv env (VSome t) (VSome t') = conv env t t'
  conv env (VEquivalent t u) (VEquivalent t' u') = do
    conv env t t'
    conv env u u'
  conv env (VAssert t) (VAssert t') = conv env t t'
  conv env (VRecord m) (VRecord m') = do
    case (keys m) == (keys m') of
         True => convList env (values m) (values m')
         False => ?convRecordErr
  conv env (VRecordLit m) (VRecordLit m') = do
    case (keys m) == (keys m') of
         True => convList env (values m) (values m')
         False => ?convRecordLitErr
  conv env (VUnion m) (VUnion m') = do
    convUnion env (toList m) (toList m')
  conv env (VCombine t u) (VCombine t' u') = do
    conv env t t'
    conv env u u'
  conv env (VCombineTypes t u) (VCombineTypes t' u') = do
    conv env t t'
    conv env u u'
  conv env (VInject m k (Just mt)) (VInject m' k' (Just mt')) = do
    convUnion env (toList m) (toList m')
    convEq k k'
    conv env mt mt'
  conv env (VInject m k Nothing) (VInject m' k' Nothing) = do
    convUnion env (toList m) (toList m')
    convEq k k'
  conv env VPrimVar VPrimVar = pure () -- TODO not in conv, maybe covered by `_ | ptrEq t t' -> True` case?
  conv env _ _ = Left ?convErr1

-- quote

countName' : Name -> List Name -> Int
countName' x env = go 0 env
where
  go : Int -> List Name -> Int
  go acc [] = acc
  go acc (x' :: xs) = go (if x == x' then acc + 1 else acc) xs

fresh : Name -> List Name -> (Name, Value)
fresh x env = (x, VVar x (countName' x env))

freshCl : Closure -> List Name -> (Name, Value, Closure)
freshCl cl@(MkClosure x _ _) env = (x, snd (fresh x env), cl)

mutual
  qVar : Name -> Int -> List Name -> Expr Void
  qVar x i env = EVar x ((countName' x env) - i - 1)

  quoteBind : Name -> List Name -> Value -> Either Error (Expr Void)
  quoteBind x env = quote (x :: env)

  qApp : List Name -> Expr Void -> Value -> Either Error (Expr Void)
  qApp env t VPrimVar = Right $ t
  qApp env t u        = Right $ EApp t !(quote env u)

  -- Prelude.foldlM : (Foldable t, Monad m) => (a -> b -> m a) -> a -> t b -> m a
  qAppM : List Name -> Expr Void -> List Value -> Either Error (Expr Void)
  qAppM env x args = foldlM (qApp env) x args

  quote : List Name -> Value -> Either Error (Expr Void)
  quote env (VConst k) = Right $ EConst k
  quote env (VVar x i) = Right $ qVar x i env
  quote env (VApp t u) = qApp env !(quote env t) u
  quote env (VLambda a b) =
    let (x, v, t) = freshCl b env in
        Right $ ELam x !(quote env a) !(quoteBind x env !(inst t v))
  quote env (VHLam Prim t) = quote env !(t VPrimVar)
  quote env (VPi a b) =
    let (x, v, b') = freshCl b env in
        Right $ EPi x !(quote env a) !(quoteBind x env !(inst b' v))
  quote env (VHPi x a b) =
    let (x', v) = fresh x env in
        Right $ EPi x !(quote env a) !(quoteBind x env !(b v))
  quote env VBool = Right $ EBool
  quote env (VBoolLit b) = Right $ EBoolLit b
  quote env (VBoolAnd t u) = Right $ EBoolAnd !(quote env t) !(quote env u)
  quote env VNatural = Right $ ENatural
  quote env (VNaturalLit k) = Right $ ENaturalLit k
  quote env (VNaturalIsZero x) = qApp env ENaturalIsZero x
  quote env VInteger = Right $ EInteger
  quote env (VIntegerLit x) = Right $ EIntegerLit x
  quote env (VIntegerNegate x) = qApp env EIntegerNegate x
  quote env VDouble = Right $ EDouble
  quote env (VDoubleLit x) = Right $ EDoubleLit x
  quote env VText = Right $ EText
  quote env (VTextLit (MkVChunks xs x)) =
    let chx = traverse (mapChunks (quote env)) xs in
    Right $ ETextLit (MkChunks !chx x)
  quote env (VList x) = qApp env EList x
  quote env (VListLit Nothing ys) =
    let ys' = traverse (quote env) ys in
    Right $ EListLit Nothing !ys'
  quote env (VListLit (Just x) ys) =
    let ys' = traverse (quote env) ys in
    Right $ EListLit (Just !(quote env x)) !ys'
  quote env (VListAppend x y) = Right $ EListAppend !(quote env x) !(quote env y)
  quote env (VListHead x y) = qAppM env EListHead [x, y]
  quote env (VOptional x) = qApp env EOptional x
  quote env (VNone x) = qApp env ENone x
  quote env (VSome x) = Right $ ESome !(quote env x)
  quote env (VEquivalent x y) = Right $ EEquivalent !(quote env x) !(quote env y)
  quote env (VAssert x) = Right $ EAssert !(quote env x)
  quote env (VRecord x) =
    let x' = traverse (quote env) x in
    Right $ ERecord !x'
  quote env (VRecordLit x) =
    let x' = traverse (quote env) x in
    Right $ ERecordLit !x'
  quote env (VUnion x) =
    let x' = traverse (mapMaybe (quote env)) x in
    Right $ EUnion !x'
  quote env (VCombine x y) = Right $ ECombine !(quote env x) !(quote env y)
  quote env (VCombineTypes x y) = Right $ ECombineTypes !(quote env x) !(quote env y)
  quote env (VInject m k Nothing) =
    let m' = traverse (mapMaybe (quote env)) m in
    Right $ EField (EUnion !m') k
  quote env (VInject m k (Just t)) =
    let m' = traverse (mapMaybe (quote env)) m in
    qApp env (EField (EUnion !m') k) t
  quote env VPrimVar = Left $ ?quoteErr1

||| destruct VPi and VHPi
vAnyPi : Value -> Either Error (Name, Ty, (Value -> Either Error Value))
vAnyPi (VHPi x a b) = Right (x, a, b)
vAnyPi (VPi a b@(MkClosure x _ _)) = Right (x, a, inst b)
vAnyPi _ = Left ?vAnyPiErr

||| returns `VConst CType`
vType : Value
vType = VConst CType

||| returns `VConst Kind`
vKind : Value
vKind = VConst Kind

||| returns `VConst Sort`
vSort : Value
vSort = VConst Sort

data Types = TEmpty
           | TBind Types Name Value

axiom : U -> Either Error U
axiom CType = Right Kind
axiom Kind = Right Sort
axiom Sort = Left ?axiomErr

rule : U -> U -> Either Error U
rule CType CType = Right CType
rule Kind CType = Right CType
rule Sort CType = Right CType
rule Kind Kind = Right Kind
rule Sort Kind = Right Sort
rule Sort Sort = Right Sort
-- This forbids dependent types. If this ever changes, then the fast
-- path in the type inference for lambdas becomes unsound.
rule _    _    = Left ?ruleErr

record Cxt where
  constructor MkCxt
  values : Env'
  types  : Types

export
initCxt : Cxt
initCxt = MkCxt Empty TEmpty

envNames : Env' -> List Name
envNames Empty = []
envNames (Skip env x) = x :: envNames env
envNames (Extend env x _) = x :: envNames env

||| Extend context with a name, its type, and its value
define : Name -> Value -> Value -> Cxt -> Cxt
define x t a (MkCxt ts as) = MkCxt (Extend ts x t) (TBind as x a)

||| Extend context with a name and its type
bind : Name -> Value -> Cxt -> Cxt
bind x a (MkCxt ts as) = MkCxt (Skip ts x) (TBind as x a)

mutual
  unify : Cxt -> Value -> Value -> Either Error ()
  unify cxt t u = conv (values cxt) t u

  ||| Check if an Expr is of type `VConst c`
  checkTy : Cxt -> Expr Void -> Either Error (Expr Void, U)
  checkTy cxt t = do
    (t, a) <- infer cxt t
    case a of
      VConst c => pure (t, c)
      _        => Left ?checkTyErr

  ||| returns the original `Expr Void` on success
  export
  check : Cxt -> Expr Void -> Value -> Either Error (Expr Void)
  check cxt (EConst CType) vKype = pure $ EConst CType
  check cxt (EConst Kind) vSort = pure $ EConst Kind
  check cxt (EConst Sort) z = Left ?checkSortErr
  check cxt (ELam x a t) pi =
    let (x', v) = fresh x (envNames (values cxt)) in do -- TODO not sure about fresh...
    (_, a', b) <- vAnyPi pi
    (a, _) <- checkTy cxt a
    av <- eval (values cxt) a
    unify cxt av a'
    t <- check (define x' v av cxt) t !(b v)
    pure $ ELam x a t
  check cxt (EBoolLit t) VBool = pure $ EBoolLit t
  check cxt (ENaturalLit t) VNatural = pure $ ENaturalLit t
  check cxt (EIntegerLit t) VInteger = pure $ EIntegerLit t
  check cxt (EDoubleLit t) VDouble = pure $ EDoubleLit t
  check cxt (ETextLit t) VText = pure $ ETextLit t
  -- check cxt (ERecordLit y) z = ?check_rhs TODO maybe add this later for performance?
  check cxt t a = do
    (t, a') <- infer cxt t
    unify cxt a' a
    pure t

  ||| returns a pair (Expr, Value), which is original Expr, and it's type as a Value
  export
  infer : Cxt -> Expr Void -> Either Error (Expr Void, Value)
  infer cxt (EConst k) = (\k' => (EConst k, VConst k')) <$> axiom k
  infer cxt (EVar x y) = go (types cxt) y
  where
    go : Types -> Int -> Either Error (Expr Void, Value)
    go TEmpty i = Left ?go_rhs_1
    go (TBind ts x' a) i =
      case x == x' of
           True => if i == 0 then Right (EVar x i, a) else go ts (i - 1)
           False => go ts i
  infer cxt (ELam x a t) = do
    (a, ak) <- checkTy cxt a
    av <- eval (values cxt) a
    (t, b) <- infer (bind x av cxt) t
    nb <- quote (x :: (envNames (values cxt))) b
    case ak of
         CType => Right (ELam x a t, (vFun av b))
         _ => Right ( ELam x a t
                    , VHPi x av $
                        \u => Right $ !(eval (Extend (values cxt) x u) nb)) -- TODO check i'm using values right
  infer cxt (EPi x a b) = do
    (a, ak) <- checkTy cxt a
    av <- eval (values cxt) a
    (b, bk) <- checkTy (bind x av cxt) b
    k' <- rule ak bk
    Right (EPi x a b, VConst k')
  infer cxt (EApp t u) = do
    (t, tt) <- infer cxt t
    (x, a, b) <- vAnyPi tt
    check cxt u a
    Right $ (EApp t u, !(b !(eval (values cxt) u)))
  infer cxt (ELet x Nothing a b) = do
    (a, aa) <- infer cxt a
    v <- eval (values cxt) a
    infer (define x aa v cxt) b
  infer cxt (ELet x (Just t) a b) = do
    tt <- eval (values cxt) t
    check cxt a tt
    v <- eval (values cxt) a
    infer (define x tt v cxt) b
  infer cxt (EAnnot x t) = do
    (t, tt) <- checkTy cxt t
    tv <- eval (values cxt) t
    check cxt x tv
    Right $ (EAnnot x t, tv)
  infer cxt EBool = Right $ (EBool, VConst CType)
  infer cxt (EBoolLit x) = Right $ (EBoolLit x, VBool)
  infer cxt (EBoolAnd x y) = do
    check cxt x VBool
    check cxt y VBool
    Right $ (EBoolAnd x y, VBool)
  infer cxt ENatural = Right $ (ENatural, VConst CType)
  infer cxt (ENaturalLit k) = Right $ (ENaturalLit k, VNatural)
  infer cxt ENaturalIsZero = Right $ (ENaturalIsZero, (vFun VNatural VBool))
  infer cxt EInteger = Right $ (EInteger, VConst CType)
  infer cxt (EIntegerLit x) = Right $ (EIntegerLit x, VInteger)
  infer cxt EIntegerNegate = Right $ (EIntegerNegate, (vFun VInteger VInteger))
  infer cxt EDouble = Right $ (EDouble, VConst CType)
  infer cxt (EDoubleLit x) = Right $ (EDoubleLit x, VDouble)
  infer cxt EText = Right $ (EText, VConst CType)
  infer cxt (ETextLit (MkChunks xs x)) =
    let go = mapChunks (\e => check cxt e VText) in do
    traverse go xs
    Right $ (ETextLit (MkChunks xs x), VText)
  infer cxt EList = do
    Right $ (EList, VConst CType)
  infer cxt (EListLit Nothing []) = do
    Left ?inferlistErr
  infer cxt (EListLit Nothing (x :: xs)) = do
    (x', ty) <- infer cxt x
    traverse (\e => check cxt e ty) xs
    Right $ (EListLit Nothing (x :: xs), VList ty)
  infer cxt (EListLit (Just x) xs) = do
    ty <- eval (values cxt) x
    traverse (\e => check cxt e ty) xs
    Right $ (EListLit (Just x) xs, VList ty)
  infer cxt (EListAppend t u) = do
    (t', tt) <- infer cxt t
    case tt of
         (VList x) => do
           check cxt u tt
           Right $ (EListAppend t u, tt)
         _ => Left ?inferlistappendErr
  infer cxt EListHead =
    Right $ (EListHead, VHPi "a" vType $ \a => Right $ vFun (VList a) a)
  infer cxt EOptional =
    Right $ (EOptional, vType)
  infer cxt (ESome t) = do
    check cxt t vType
    (t, tt) <- infer cxt t
    pure (ESome t, VOptional tt)
  infer cxt ENone =
    Right $ (ENone, VHPi "a" vType $ \a => Right $ vFun (VOptional a) a)
  infer cxt e@(EEquivalent t u) = do
    (t, tt) <- infer cxt t
    check cxt u tt
    -- conv (values cxt) tt vType TODO
    Right (e, vType)
  infer cxt (EAssert (EEquivalent a b)) = do
    (a, aa) <- infer cxt a
    av <- eval (values cxt) a
    bv <- eval (values cxt) b
    conv (values cxt) av bv
    pure (EAssert (EEquivalent a b), VEquivalent av bv)
  infer cxt (EAssert _) = Left ?inferAsserErr2
  infer cxt (ERecord x) = do
    xs' <- traverse (inferSkip cxt) x
    Right $ (ERecord x, getHighestType xs')
  infer cxt (ERecordLit x) = do
    xs' <- traverse (inferSkip cxt) x
    Right $ (ERecordLit x, VRecordLit xs')
  infer cxt (EUnion x) = do
    xs' <- traverse (mapMaybe (inferSkip cxt)) x
    Right $ (EUnion x, getHighestTypeM xs')
  infer cxt (ECombine t u) = do
    (t, tt) <- infer cxt t
    (u, uu) <- infer cxt u
    case (tt, uu) of
         (VRecord a', VRecord b') => do
           ty <- mergeWithApp doCombine a' b'
           Right $ (ECombine t u, VRecord ty)
         _ => Left ?inferCombineErr
  infer cxt (ECombineTypes a b) = do
    av <- eval (values cxt) a
    bv <- eval (values cxt) b
    case (av, bv) of
         (VRecord a', VRecord b') => do
           ty <- mergeWithApp doCombine a' b'
           Right $ (ECombineTypes a b, getHighestType ty)
         _ => Left ?inferCombineTypesErr
         {-
    let xs = toList x in do
      synth ctx u
      xs' <- traverse (mapUnion (eval (mkEnv ctx))) xs
      xsRb <- traverse (mapUnion (readBackTyped ctx (VConst CType))) xs'
      case lookup k xs' of
           Nothing => Left (FieldNotFoundError "k")
           (Just Nothing) => Right (VUnion (fromList xs'))
           (Just (Just x')) =>
              Right (vFun x' (VUnion (fromList xs')))
              -}
  infer cxt (EField t@(EUnion x) k) = do
    xv <- traverse (mapMaybe (eval (values cxt))) x
    case lookup k xv of
         Nothing => Left ?inferFieldNotFound
         (Just Nothing) => Right $ (EField t k, VUnion xv)
         (Just (Just y)) => Right $ (EField t k, (vFun y (VUnion xv)))
  infer cxt (EField t k) = Left ?inferWrongFieldType
  -- synth ctx (EEmbed (Raw x)) = absurd x
  -- synth ctx (EEmbed (Resolved x)) = synth initCtx x -- Using initCtx here to ensure fresh context.
  infer cxt (EEmbed (Raw x)) = absurd x
  infer cxt (EEmbed (Resolved x)) = infer initCxt x

  ||| infer but only return `Value`, not `(Expr Void, Value)`
  inferSkip : Cxt -> Expr Void -> Either Error Value
  inferSkip cxt = (\e => Right $ snd !(infer cxt e))

  pickHigherType : (acc : Ty) -> Ty -> Ty
  pickHigherType (VConst CType) (VConst Kind) = VConst Kind
  pickHigherType _ (VConst Sort) = VConst Sort
  pickHigherType acc _ = acc

  getHighestTypeM : Foldable t => t (Maybe Value) -> Value
  getHighestTypeM x = foldl go vType x
  where
    go : Value -> Maybe Value -> Value
    go x Nothing = x
    go x (Just y) = pickHigherType x y

  getHighestType : Foldable t => t Value -> Value
  getHighestType x = foldl pickHigherType vType x
