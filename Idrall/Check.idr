module Idrall.Check

import Idrall.Expr
import Idrall.Error
import Idrall.Value
import Idrall.Map

import Data.List
import Data.List1
import Data.Strings

-- alpha equivalence
nestError : Either Error b -> Error -> Either Error b
nestError x e =
  case x of
       (Left e') => Left $ NestedError e e'
       (Right x') => Right x'

||| returns `VConst CType`
vType : Value
vType = VConst CType

||| returns `VConst Kind`
vKind : Value
vKind = VConst Kind

||| returns `VConst Sort`
vSort : Value
vSort = VConst Sort

-- evaluator
mutual
  inst : Closure -> Value -> Either Error Value
  inst = evalClosure

  covering
  evalClosure : Closure -> Value -> Either Error Value
  evalClosure (MkClosure x env e) v
    = do eval (Extend env x v) e

  evalVar : Env -> Name -> Int -> Either Error Value
  evalVar Empty x i = pure $ VVar x (0 - i - 1)
  evalVar (Skip env x') x i =
    case x == x' of
         True => if i == 0 then pure $ VVar x (countName x env) else evalVar env x (i - 1)
         False => evalVar env x i
  evalVar (Extend env x' v) x i =
    case x == x' of
         True => if i == 0 then pure v else evalVar env x (i - 1)
         False => evalVar env x i

  vVar : Env -> Name -> Int -> Either Error Value
  vVar = evalVar

  export
  covering
  eval : Env -> Expr Void -> Either Error Value
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
  eval env (EBoolLit b) = Right (VBoolLit b)
  eval env (EBoolAnd t u) =
    case (!(eval env t), !(eval env u)) of
         (VBoolLit True, u) => pure u
         (VBoolLit False, u) => pure $ VBoolLit False
         (t, VBoolLit True) => pure t
         (t, VBoolLit False) => pure $ VBoolLit False
         (t, u) => case conv env t u of
                        Right _ => Right t
                        Left _ => Right $ VBoolAnd t u
  eval env (EBoolOr t u) =
    case (!(eval env t), !(eval env u)) of
         (VBoolLit False, u) => pure u
         (VBoolLit True, u) => pure $ VBoolLit True
         (t, VBoolLit False) => pure t
         (t, VBoolLit True) => pure $ VBoolLit True
         (t, u) => case conv env t u of
                        Right _ => pure t
                        Left _ => pure $ VBoolOr t u
  eval env (EBoolEQ t u) =
    case (!(eval env t), !(eval env u)) of
         (VBoolLit True, u) => pure u
         (t, VBoolLit True) => pure t
         (t, u) => case conv env t u of
                        Right _ => pure $ VBoolLit True
                        Left _ => pure $ VBoolEQ t u
  eval env (EBoolNE t u) =
    case (!(eval env t), !(eval env u)) of
         (VBoolLit False, u) => pure u
         (t, VBoolLit False) => pure t
         (t, u) => case conv env t u of
                        Right _ => pure $ VBoolLit False
                        Left _ => pure $ VBoolNE t u
  eval env ENatural = Right VNatural
  eval env (ENaturalLit k) = Right (VNaturalLit k)
  eval env ENaturalBuild =
    pure $ VPrim $
      \c => case c of
                 VHLam (NaturalFoldCl x) _ => pure x
                 VPrimVar => pure $ VNaturalBuild VPrimVar
                 t => vAppM t [ VNatural
                              , VHLam (Typed "n" VNatural) $ \n =>
                                    pure $ vNaturalPlus n (VNaturalLit 1)
                              , VNaturalLit 0
                              ]
  eval env ENaturalFold =
    pure $ VPrim $
      \c => case c of
                 VNaturalLit n =>
                     pure $ VHLam (Typed "natural" vType) $ \natural =>
                     pure $ VHLam (Typed "succ" (vFun natural natural) ) $ \succ =>
                     pure $ VHLam (Typed "zero" natural) $ \zero =>
                       go succ zero n
                 n =>
                     pure $ VHLam (NaturalFoldCl n) $ \natural =>
                     pure $ VPrim $ \succ =>
                     pure $ VPrim $ \zero =>
                     pure $ VNaturalFold n natural succ zero
  where
    go : Value -> Value -> Nat -> Either Error Value
    go succ acc 0 = pure acc
    go succ acc (S k) = go succ !(vApp succ acc) k
  eval env ENaturalIsZero = Right $ VPrim $
                              \c => case c of
                                      VNaturalLit n => Right $ VBoolLit (n == 0)
                                      n             => Right $ VNaturalIsZero n
  eval env (EBoolIf b t f) =
    case (!(eval env b), !(eval env t), !(eval env f)) of
         (VBoolLit True, t, f) => pure t
         (VBoolLit False, t, f) => pure f
         (b, VBoolLit True, VBoolLit False) => pure b
         (b, t, f) => case conv env t f of
                           (Right _) => pure t
                           (Left _) => pure $ VBoolIf b t f
  eval env ENaturalEven =
    Right $ VPrim $
      \c => case c of
                 VNaturalLit n => pure $ VBoolLit (isEven n)
                 n             => pure $ VNaturalEven n
  eval env ENaturalOdd =
    Right $ VPrim $
      \c => case c of
                 VNaturalLit n => pure $ VBoolLit (isOdd n)
                 n             => pure $ VNaturalOdd n
  eval env ENaturalSubtract = do
    Right $ VPrim $
      \x => Right $ VPrim $
        \y => case (x, y) of
                   (VNaturalLit n, VNaturalLit n') => pure $ VNaturalLit (minus n' n)
                   (n, n') => pure $ VNaturalSubtract n' n'
  eval env ENaturalShow =
    Right $ VPrim $
      \c => case c of
                 VNaturalLit n => pure $ VTextLit (MkVChunks [] (show n))
                 n             => pure $ VNaturalShow n
  eval env ENaturalToInteger =
    Right $ VPrim $
      \c => case c of
                 VNaturalLit n => pure $ VIntegerLit (cast n)
                 n             => pure $ VNaturalToInteger n
  eval env (ENaturalPlus t u) = pure $ vNaturalPlus !(eval env t) !(eval env u)
  eval env (ENaturalTimes t u) =
    case (!(eval env t), !(eval env u)) of
         (VNaturalLit 1, u) => pure u
         (t, VNaturalLit 1) => pure t
         (VNaturalLit 0, u) => pure $ VNaturalLit 0
         (t, VNaturalLit 0) => pure $ VNaturalLit 0
         (VNaturalLit t, VNaturalLit u) => pure (VNaturalLit $ t * u)
         (t, u) => pure $ VNaturalTimes t u
  eval env EInteger = Right VInteger
  eval env (EIntegerLit k) = Right (VIntegerLit k)
  eval env EIntegerShow =
    Right $ VPrim $
      \c => case c of
                 VIntegerLit n => pure $ VTextLit (MkVChunks [] (show n))
                 n             => pure $ VIntegerShow n
  eval env EIntegerNegate = Right $ VPrim $
                            \c => case c of
                                       VIntegerLit n => Right $ VIntegerLit (negate n)
                                       n             => Right $ VIntegerNegate n
  eval env EIntegerClamp =
    Right $ VPrim $
      \c => case c of
                 VIntegerLit n => pure $ VNaturalLit (integerToNat n)
                 n             => pure $ VIntegerClamp n
  eval env EIntegerToDouble =
    Right $ VPrim $
      \c => case c of
                 VIntegerLit n => pure $ VDoubleLit (cast n)
                 n             => pure $ VIntegerToDouble n
  eval env EDouble = Right VDouble
  eval env (EDoubleLit k) = Right (VDoubleLit k)
  eval env EDoubleShow =
    Right $ VPrim $
      \c => case c of
                 VDoubleLit n => pure $ VTextLit (MkVChunks [] (show n))
                 n             => pure $ VDoubleShow n
  eval env EText = Right VText
  eval env (ETextLit (MkChunks xs x)) = do
    xs' <- traverse (mapChunks (eval env)) xs
    Right (VTextLit (MkVChunks xs' x))
  eval env (ETextAppend x y) =
    case (!(eval env x), !(eval env y)) of
         (VTextLit (MkVChunks [] ""), u) => pure u
         (t, VTextLit (MkVChunks [] "")) => pure t
         (VTextLit x, VTextLit y) => pure $ VTextLit (x <+> y)
         (t, u) => pure $ VTextAppend t u
  eval env ETextShow =
    pure $ VPrim $ \c =>
      case c of
           VTextLit (MkVChunks [] x) => pure $ VTextLit (MkVChunks [] (vTextShow x))
           t => pure $ VTextShow t
  eval env ETextReplace = -- Probably not right
    pure $ VPrim $
      \needle => pure $ VPrim $
        \replacement => pure $ VPrim $
          \haystack =>
            case needle of
                 VTextLit (MkVChunks [] "") => pure haystack
                 VTextLit (MkVChunks [] needleText) =>
                   case haystack of
                        (VTextLit (MkVChunks [] haystackText)) =>
                          case replacement of
                               (VTextLit (MkVChunks [] replacementText)) =>
                                 pure $ VTextLit $
                                        MkVChunks [] $ textReplace needleText replacementText haystackText
                               (VTextLit (MkVChunks chx replacementText)) =>
                                 case strFromChunks chx  of
                                      Nothing => Left $ ErrorMessage "could not make string for replacement"
                                      (Just str) =>
                                         pure $ VTextLit $
                                         MkVChunks [] $ textReplace
                                                          needleText
                                                          replacementText
                                                          haystackText
                               _ => pure $ VTextReplace needle replacement haystack
                        _ => pure $ VTextReplace needle replacement haystack
                 k => pure $ VTextReplace needle replacement haystack
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
    vListAppend x' y'
  eval env EListBuild =
    Right $ VPrim $
      \a => Right $ VPrim $
        \c => case c of
                   -- VHLam (ListFoldCl x) _ => pure $ x
                   VPrimVar => pure $ VListBuild a VPrimVar
                   t => vAppM t [ VList a
                                , VHLam (Typed "a" a) $ \x =>
                                    pure $ VHLam (Typed "as" (VList a)) $ \as =>
                                      vListAppend (VListLit Nothing [x]) as
                                , VListLit (Just a) []
                                ]
  eval env EListFold =
    Right $ VPrim $
      \a => Right $ VPrim $
        \c => case c of
                   (VListLit _ as) =>
                     Right $ VHLam (Typed "list" vType) $ \list =>
                     Right $ VHLam (Typed "cons" (vFun a $ vFun list list) ) $ \cons =>
                     Right $ VHLam (Typed "nil"  list) $ \nil =>
                       -- foldlM (\x,b => (vApp !(vApp cons x) b)) nil as
                       foldrM (\x,b => vAppM cons [x, b]) nil as
                   as => Right $ VHLam (ListFoldCl as) $
                        \t => Right $ VPrim $
                        \c' => Right $ VPrim $
                        \n => Right $ VListFold a as t c' n
    where
      foldrM : (Foldable t, Monad m) => (funcM: b -> a -> m a) -> (init: a) -> (input: t b) -> m a
      foldrM fm a0 = foldr (\b,ma => ma >>= fm b) (pure a0)
  eval env EListLength =
    Right $ VPrim $
      \a => Right $ VPrim $
        \c => case c of
                   (VListLit _ as) => pure $ VNaturalLit (length as)
                   as => pure $ VListLength a as
  eval env EListHead =
    Right $ VPrim $ \a =>
      Right $ VPrim $
             \c => case c of
                        VListLit _ [] => pure $ VNone a
                        VListLit _ (h :: _) => pure $ VSome h
                        as => pure $ VListHead a as
  eval env EListLast =
    Right $ VPrim $
      \a => Right $ VPrim $
        \c => case c of
                   VListLit _ as =>
                     case last' as of
                          Nothing => pure $ VNone a
                          (Just t) => pure $ VSome t
                   as => pure $ VListLast a as
  eval env EListIndexed =
    pure $ VPrim $
      \a => Right $ VPrim $
        \c => case c of
                   VListLit t as => pure $ vListIndexed t as
                   as => pure $ VListLast a as
  eval env EListReverse =
    pure $ VPrim $
      \a => Right $ VPrim $
        \c => case c of
                   VListLit t as => pure $ VListLit t (reverse as)
                   as => pure $ VListReverse a as
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
  eval env (EPrefer x y) = do
    x' <- eval env x
    y' <- eval env y
    doPrefer x' y'
  eval env (EMerge x y ma) = -- TODO Double check this
    case (!(eval env x), !(eval env y), !(mapMaybe (eval env) ma)) of
         (VRecordLit m, VInject _ k (Just t), _) =>
           case lookup k m of
                Just f => vApp f t
                Nothing => Left $ MergeUnhandledCase $ show k -- TODO DRY these error conditions
         (VRecordLit m, VInject _ k _, _) =>
           case lookup k m of
                Just t => pure t
                Nothing => Left $ MergeUnhandledCase $ show k
         (VRecordLit m, VSome t, _) =>
           case lookup (MkFieldName "Some") m of
                Just f => vApp f t
                Nothing => Left $ MergeUnhandledCase $ "Some"
         (VRecordLit m, VNone _, _) =>
           case lookup (MkFieldName "None") m of
                Just t => pure t
                Nothing => Left $ MergeUnhandledCase $ "None"
         (t, u, ma) => pure $ VMerge t u ma
  eval env (EUnion x) =
    let xs = toList x in
    do xs' <- traverse (mapUnion (eval env)) xs
       Right (VUnion (fromList xs'))
  eval env (EField (EUnion x) k) =
    let xs = toList x in do
      x' <- traverse (mapUnion (eval env)) xs
      case lookup k x' of
           Nothing => Left (FieldNotFoundError $ show k)
           (Just Nothing) => Right (VInject (fromList x') k Nothing)
           (Just (Just _)) => Right (VPrim $ \u => Right $ VInject (fromList x') k (Just u))
  eval env (EField (ERecordLit m) k) = do
    m' <- traverse (eval env) m
    case lookup k m' of
         Nothing => Left (FieldNotFoundError $ show k)
         (Just t) => pure t
  eval env (EField x k) = Left (InvalidFieldType (show x))
  eval env (ERecordCompletion t u) =
    eval env (EAnnot (EPrefer (EField t (MkFieldName "default")) u) (EField t (MkFieldName "Type")))
  eval env (EToMap x Nothing) =
    case !(eval env x) of
         VRecordLit ms =>
           let xs = SortedMap.toList ms in
               case xs of
                    [] => Left $ ToMapEmpty "Needs an annotation"
                    (y :: ys) => pure $ VListLit Nothing $ map vToMap (y :: ys)
         other => pure $ VToMap other Nothing
  eval env (EToMap x (Just y)) = do
    y' <- eval env y
    case !(eval env x) of
         VRecordLit ms => pure $ VListLit (Just y') $ map vToMap (SortedMap.toList ms)
         other => pure $ VToMap other Nothing
  eval env (EProject x (Left ks)) =
    case !(eval env x) of
         VRecordLit ms => pure $ VRecordLit $ fromList !(vProjectByFields ms ks)
         other => Left (Unexpected $ "Not a RecordLit. Value: " ++ show other)
  eval env (EProject x (Right y)) =
    case (!(eval env x), !(eval env y)) of
         (VRecordLit ms, VRecordLit ms') => pure $ VRecordLit $ fromList !(vProjectByFields ms (keys ms'))
         (other, VRecord _) => Left (Unexpected $ "Not a RecordLit. Value: " ++ show other)
         (_, other) => Left (Unexpected $ "Not a Record. Value: " ++ show other)
  eval env (EWith x ks y) = vWith !(eval env x) ks !(eval env y)
  eval env (EEmbed (Raw x)) = absurd x
  eval env (EEmbed (Resolved x)) = eval Empty x

  vTextShow : String -> String
  vTextShow x = "\"" <+> (foldl (<+>) "" (map f (unpack x))) <+> "\""
  where
    f : Char -> String
    f '"'  = "\\\""
    f '$'  = "\\u0024"
    f '\\' = "\\\\"
    f '\b' = "\\b"
    f '\n' = "\\n"
    f '\r' = "\\r"
    f '\t' = "\\t"
    f '\f' = "\\f"
    -- TODO handle this case
    -- https://github.com/dhall-lang/dhall-haskell/blob/f33e8cff8fc51e4a562f48fcf987e6af5e09142d/dhall/src/Dhall/Eval.hs#L847
    f c = case c <= '\x1F' of
               True => singleton c
               False => singleton c

  vToMap : (FieldName, Value) -> Value
  vToMap (MkFieldName k, v) = VRecordLit $ fromList
    [ (MkFieldName "mapKey", VTextLit $ MkVChunks [] k)
    , (MkFieldName "mapValue", v)
    ]

  vWith : Value -> List1 FieldName -> Value -> Either Error Value
  vWith (VRecordLit ms) (head ::: []) u = pure $ VRecordLit $ insert head u ms
  vWith (VRecordLit ms) (head ::: (k :: ks)) u =
    case lookup head ms of
         Nothing =>
           let new = VRecordLit (fromList [])
               rest = vWith new (k ::: ks) u
           in
           pure $ VRecordLit $ insert head !rest ms
         (Just u') =>
           let rest = vWith u' (k ::: ks) u in
           pure $ VRecordLit $ insert head !rest ms
  vWith t ks u = pure $ VWith t ks u

  vProjectByFields : SortedMap FieldName Value -> List FieldName -> Either Error (List (FieldName, Value))
  vProjectByFields ms ks = traverse (lookupRecord ms) ks
  where
    lookupRecord : SortedMap FieldName Value -> FieldName -> Either Error (FieldName, Value)
    lookupRecord ms k = case lookup k ms of
                             Nothing => Left $ FieldNotFoundError $ show k
                             (Just v) => pure (k, v)

  listIndexedType : Maybe Value -> Maybe Value
  listIndexedType Nothing = Nothing
  listIndexedType (Just a) =
    Just $ VRecord (fromList [(MkFieldName "index", VNatural), (MkFieldName "value", a)])

  vNaturalPlus : Value -> Value -> Value
  vNaturalPlus (VNaturalLit 0) u = u
  vNaturalPlus t (VNaturalLit 0) = t
  vNaturalPlus (VNaturalLit t) (VNaturalLit u) = VNaturalLit $ t + u
  vNaturalPlus t u = VNaturalPlus t u

  -- TODO lots of traversals here
  vListIndexed : Maybe Value -> List Value -> Value
  vListIndexed a xs =
    let prep = foldl go [] xs
        lists = map toRecordList prep
        recordsAsLists = map toRecordList prep
        final = map toRecord recordsAsLists
        in VListLit (listIndexedType a) final
  where
    go : List (Nat, Value) -> Value -> List (Nat, Value)
    go [] t = [(0, t)]
    go acc@((i, _) :: _) u = (i+1, u) :: acc
    toRecordList : (Nat, Value) -> List (FieldName, Value)
    toRecordList (i, v) = [(MkFieldName "index", VNaturalLit i), (MkFieldName "value", v)]
    toRecord : List (FieldName, Value) -> Value
    toRecord xs = VRecordLit $ fromList xs

  covering
  doApply : Value -> Value -> Either Error Value
  doApply (VLambda ty closure) arg =
    evalClosure closure arg
  doApply (VHLam i f) arg = (f arg)
  doApply f arg = Right $ VApp f arg

  vApp : Value -> Value -> Either Error Value
  vApp = doApply

  vAppM : Value -> List Value -> Either Error Value
  vAppM x xs = foldlM vApp x xs

  covering
  doAssert : Env -> Value -> Either Error Value
  doAssert env v@(VEquivalent t u) = do
    conv env t u
    pure $ VAssert v
  doAssert env x = Left (AssertError ("not an equivalence type: " ++ show x))

  vListAppend : Value -> Value -> Either Error Value
  vListAppend (VListLit _ []) u = Right u
  vListAppend t (VListLit _ []) = Right t
  vListAppend (VListLit t xs) (VListLit _ ys) =
    Right (VListLit t (xs ++ ys))
  vListAppend x y = Right $ VListAppend x y

  doCombine : Value -> Value -> Either Error Value
  doCombine (VRecordLit x) (VRecordLit y) =
    Right (VRecordLit $ !(mergeWithApp doCombine x y))
  doCombine (VRecord x) (VRecord y) =
    Right (VRecord $ !(mergeWithApp doCombine x y))
  doCombine x y = Right $ VCombineTypes x y

  doPrefer : Value -> Value -> Either Error Value
  doPrefer (VRecordLit x) (VRecordLit y) =
    Right (VRecordLit $ !(mergeWithApp' doPrefer x y))
  doPrefer x y = Right $ VPrefer x y

  -- conversion checking
  -- Needs to be in mutual block with eval because it's used by Bool builtins

  countName : Name -> Env -> Int
  countName x env = go 0 env
  where
    go : (acc : Int) -> Env -> Int
    go acc Empty = acc
    go acc (Skip env x') = go (if x == x' then acc + 1 else acc) env
    go acc (Extend env x' _) = go (if x == x' then acc + 1 else acc) env

  convFresh : Name -> Env -> (Name, Value)
  convFresh x env = (x, VVar x (countName x env))

  convFreshCl : Closure -> Env -> (Name, Value, Closure)
  convFreshCl cl@(MkClosure x _ _) env = (x, snd (convFresh x env), cl)

  convErr : (Show x) => x -> x -> Either Error a
  convErr x y = Left $ AlphaEquivError $ show x ++ "\n not alpha equivalent to:\n" ++ show y

  strFromChunks : List (String, Value) -> Maybe String
  strFromChunks [] = Just neutral
  strFromChunks ((str, (VTextLit (MkVChunks xys' y))) :: xs') = do
    rest <- strFromChunks xs'
    mid <- strFromChunks xys'
    Just (str ++ mid ++ y ++ rest)
  strFromChunks ((str, _) :: xs') = Nothing

  convChunks : Env -> VChunks -> VChunks -> Either Error ()
  convChunks env (MkVChunks [] z) (MkVChunks [] z') = convEq z z'
  convChunks env (MkVChunks ((s, t) :: xys) z) (MkVChunks ((s', t') :: xys') z') = do
    convEq s s'
    conv env t t'
    convChunks env (MkVChunks xys z) (MkVChunks xys' z')
  convChunks env t u = convErr t u

  convList : Env -> List Value -> List Value -> Either Error ()
  convList env [] [] = pure ()
  convList env (t :: xs) (t' :: xs') = do
    conv env t t'
    convList env xs xs'
  convList env t u = convErr t u

  convUnion : Env -> List (FieldName, Maybe Value) -> List (FieldName, Maybe Value) -> Either Error ()
  convUnion env [] [] = pure ()
  convUnion env ((x, Just t) :: xs) ((x', Just t') :: ys) = do
    convEq x x'
    conv env t t'
    convUnion env xs ys
  convUnion env ((x, Nothing) :: xs) ((x', Nothing) :: ys) = do
    convEq x x'
    convUnion env xs ys
  convUnion env t u = convErr t u

  convEq : (Eq x, Show x) => x -> x -> Either Error ()
  convEq a b =
    case a == b of
         True => Right ()
         False => convErr a b

  convSkip : Env -> Name -> Value -> Value -> Either Error ()
  convSkip env x = conv (Skip env x)

  conv : Env -> Value -> Value -> Either Error ()
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

  conv env (VConst k) (VConst k') = convEq k k'
  conv env (VVar x i) (VVar x' i') = do
    convEq x x'
    convEq i i'

  conv env (VApp t u) (VApp t' u') = do
    conv env t t'
    conv env u u'
  conv env VBool VBool = pure ()
  conv env (VBoolLit b) (VBoolLit b') = convEq b b'
  conv env (VBoolAnd t u) (VBoolAnd t' u') = do
    conv env t t'
    conv env u u'
  conv env (VBoolOr t u) (VBoolOr t' u') = do
    conv env t t'
    conv env u u'
  conv env (VBoolEQ t u) (VBoolEQ t' u') = do
    conv env t t'
    conv env u u'
  conv env (VBoolNE t u) (VBoolNE t' u') = do
    conv env t t'
    conv env u u'
  conv env (VBoolIf b t f) (VBoolIf b' t' f') = do
    conv env b b'
    conv env t t'
    conv env f f'
  conv env VNatural VNatural = pure ()
  conv env (VNaturalLit k) (VNaturalLit k') = convEq k k'
  conv env (VNaturalBuild t) (VNaturalBuild t') = conv env t t'
  conv env (VNaturalFold t u v w) (VNaturalFold t' u' v' w') = do
    conv env t t'
    conv env u u'
    conv env v v'
    conv env w w'
  conv env (VNaturalIsZero t) (VNaturalIsZero t') = conv env t t'
  conv env (VNaturalEven t) (VNaturalEven t') = conv env t t'
  conv env (VNaturalOdd t) (VNaturalOdd t') = conv env t t'
  conv env (VNaturalShow t) (VNaturalShow t') = conv env t t'
  conv env (VNaturalSubtract t u) (VNaturalSubtract t' u') = do
    conv env t t'
    conv env u u'
  conv env (VNaturalToInteger t) (VNaturalToInteger t') = conv env t t'
  conv env (VNaturalPlus t u) (VNaturalPlus t' u') = do
    conv env t t'
    conv env u u'
  conv env (VNaturalTimes t u) (VNaturalTimes t' u') = do
    conv env t t'
    conv env u u'
  conv env VInteger VInteger = pure ()
  conv env (VIntegerLit t) (VIntegerLit t') = convEq t t'
  conv env (VIntegerShow t) (VIntegerShow t') = conv env t t'
  conv env (VIntegerNegate t) (VIntegerNegate t') = conv env t t'
  conv env (VIntegerClamp t) (VIntegerClamp t') = conv env t t'
  conv env (VIntegerToDouble t) (VIntegerToDouble t') = conv env t t'
  conv env VDouble VDouble = pure ()
  conv env (VDoubleLit t) (VDoubleLit t') = convEq t t' -- TODO use binary encode
  conv env (VDoubleShow t) (VDoubleShow t') = conv env t t'
  conv env VText VText = pure ()
  conv env (VTextLit t@(MkVChunks xys z)) (VTextLit u@(MkVChunks xys' z')) =
    let l = strFromChunks xys
        r = strFromChunks xys' in
    case (l, r) of
         ((Just l'), (Just r')) => do
           convEq (l' ++ z) (r' ++ z')
         _ => convChunks env t u
  conv env (VTextAppend t u) (VTextAppend t' u') = do
    conv env t t'
    conv env u u'
  conv env (VTextShow t) (VTextShow t') = do
    conv env t t'
  conv env (VTextReplace t u v) (VTextReplace t' u' v') = do
    conv env t t'
    conv env u u'
    conv env v v'
  conv env (VList a) (VList a') = conv env a a'
  conv env (VListLit _ xs) (VListLit _ xs') = convList env xs xs'
  conv env (VListAppend t u) (VListAppend t' u') = do
    conv env t t'
    conv env u u'
  conv env (VListBuild _ t) (VListBuild _ t') = conv env t t'
  conv env (VListFold a l _ t u) (VListFold a' l' _ t' u') = do
    conv env a a'
    conv env l l'
    conv env t t'
    conv env u u'
  conv env (VListLength _ t) (VListLength _ t') = conv env t t'
  conv env (VListHead _ t) (VListHead _ t') = conv env t t'
  conv env (VListLast _ t) (VListLast _ t') = conv env t t'
  conv env (VListIndexed _ t) (VListIndexed _ t') = conv env t t'
  conv env (VListReverse _ t) (VListReverse _ t') = conv env t t'
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
         False => convErr m m'
  conv env (VRecordLit m) (VRecordLit m') = do
    case (keys m) == (keys m') of
         True => convList env (values m) (values m')
         False => convErr m m'
  conv env (VUnion m) (VUnion m') = do
    convUnion env (toList m) (toList m')
  conv env (VCombine t u) (VCombine t' u') = do
    conv env t t'
    conv env u u'
  conv env (VCombineTypes t u) (VCombineTypes t' u') = do
    conv env t t'
    conv env u u'
  conv env (VPrefer t u) (VPrefer t' u') = do
    conv env t t'
    conv env u u'
  conv env (VMerge t u Nothing) (VMerge t' u' Nothing) = do
    conv env t t'
    conv env u u'
  conv env (VMerge t u (Just a)) (VMerge t' u' (Just a')) = do
    conv env t t'
    conv env u u'
    conv env a a'
  conv env (VToMap t Nothing) (VToMap t' Nothing) = do
    conv env t t'
  conv env (VToMap t (Just a)) (VToMap t' (Just a')) = do
    conv env t t'
    conv env a a'
  conv env (VInject m k (Just mt)) (VInject m' k' (Just mt')) = do
    convUnion env (toList m) (toList m')
    convEq k k'
    conv env mt mt'
  conv env (VInject m k Nothing) (VInject m' k' Nothing) = do
    convUnion env (toList m) (toList m')
    convEq k k'
  conv env (VProject t (Left ks)) (VProject t' (Left ks')) = do
    conv env t t'
    convEq ks ks'
  conv env (VProject t (Right u)) (VProject t' (Right u')) = do
    conv env t t'
    conv env u u'
  conv env (VWith t ks u) (VWith t' ks' u') = do
    conv env t t'
    convEq ks ks'
    conv env u u'
  conv env VPrimVar VPrimVar = pure () -- TODO not in conv, maybe covered by `_ | ptrEq t t' -> True` case?
  conv env t u = convErr t u

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
  quote env (VHLam (Typed x a) t) =
    let (x', v) = fresh x env in
    Right $ ELam x' !(quote env a) !(quoteBind x env !(t v))
  quote env (VHLam _ t) = quote env !(t VPrimVar)
  quote env (VPi a b) =
    let (x, v, b') = freshCl b env in
        Right $ EPi x !(quote env a) !(quoteBind x env !(inst b' v))
  quote env (VHPi x a b) =
    let (x', v) = fresh x env in
        Right $ EPi x !(quote env a) !(quoteBind x env !(b v))
  quote env VBool = pure $ EBool
  quote env (VBoolLit b) = pure $ EBoolLit b
  quote env (VBoolAnd t u) = pure $ EBoolAnd !(quote env t) !(quote env u)
  quote env (VBoolOr t u) = pure $ EBoolOr !(quote env t) !(quote env u)
  quote env (VBoolEQ t u) = pure $ EBoolEQ !(quote env t) !(quote env u)
  quote env (VBoolNE t u) = pure $ EBoolNE !(quote env t) !(quote env u)
  quote env (VBoolIf b t f) = pure $ EBoolIf !(quote env b) !(quote env t) !(quote env f)
  quote env VNatural = Right $ ENatural
  quote env (VNaturalLit k) = Right $ ENaturalLit k
  quote env (VNaturalBuild x) = qApp env ENaturalBuild x
  quote env (VNaturalFold w x y z) = qAppM env ENaturalFold [w, x, y, z]
  quote env (VNaturalIsZero x) = qApp env ENaturalIsZero x
  quote env (VNaturalEven x) = qApp env ENaturalEven x
  quote env (VNaturalOdd x) = qApp env ENaturalOdd x
  quote env (VNaturalToInteger x) = qApp env ENaturalToInteger x
  quote env (VNaturalSubtract x y) = qAppM env ENaturalSubtract [x, y]
  quote env (VNaturalShow x) = qApp env ENaturalShow x
  quote env (VNaturalPlus t u) = Right $ ENaturalPlus !(quote env t) !(quote env u)
  quote env (VNaturalTimes t u) = Right $ ENaturalTimes !(quote env t) !(quote env u)
  quote env VInteger = Right $ EInteger
  quote env (VIntegerLit x) = Right $ EIntegerLit x
  quote env (VIntegerShow x) = qApp env EIntegerShow x
  quote env (VIntegerNegate x) = qApp env EIntegerNegate x
  quote env (VIntegerClamp x) = qApp env EIntegerClamp x
  quote env (VIntegerToDouble x) = qApp env EIntegerToDouble x
  quote env VDouble = Right $ EDouble
  quote env (VDoubleLit x) = Right $ EDoubleLit x
  quote env (VDoubleShow x) = qApp env EDoubleShow x
  quote env VText = Right $ EText
  quote env (VTextLit (MkVChunks xs x)) =
    let chx = traverse (mapChunks (quote env)) xs in
    Right $ ETextLit (MkChunks !chx x)
  quote env (VTextAppend t u) = pure $ ETextAppend !(quote env t) !(quote env u)
  quote env (VTextShow t) = qApp env ETextShow t
  quote env (VTextReplace t u v) = qAppM env ETextReplace [t, u, v]
  quote env (VList x) = qApp env EList x
  quote env (VListLit Nothing ys) =
    let ys' = traverse (quote env) ys in
    Right $ EListLit Nothing !ys'
  quote env (VListLit (Just x) ys) =
    let ys' = traverse (quote env) ys in
    Right $ EListLit (Just !(quote env x)) !ys'
  quote env (VListAppend x y) = Right $ EListAppend !(quote env x) !(quote env y)
  quote env (VListBuild t u) = qAppM env EListBuild [t, u]
  quote env (VListFold a l t u v) = qAppM env EListFold [a, l, t, u, v]
  quote env (VListLength t u) = qAppM env EListLength [t, u]
  quote env (VListHead t u) = qAppM env EListHead [t, u]
  quote env (VListLast t u) = qAppM env EListLast [t, u]
  quote env (VListIndexed t u) = qAppM env EListIndexed [t, u]
  quote env (VListReverse t u) = qAppM env EListReverse [t, u]
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
  quote env (VPrefer x y) = Right $ EPrefer !(quote env x) !(quote env y)
  quote env (VMerge x y Nothing) = pure $ EMerge !(quote env x) !(quote env y) Nothing
  quote env (VMerge x y (Just z)) = pure $ EMerge !(quote env x) !(quote env y) (Just !(quote env z))
  quote env (VToMap x Nothing) = pure $ EToMap !(quote env x) Nothing
  quote env (VToMap x (Just y)) = pure $ EToMap !(quote env x) (Just !(quote env y))
  quote env (VInject m k Nothing) =
    let m' = traverse (mapMaybe (quote env)) m in
    Right $ EField (EUnion !m') k
  quote env (VInject m k (Just t)) =
    let m' = traverse (mapMaybe (quote env)) m in
    qApp env (EField (EUnion !m') k) t
  quote env (VProject t (Left ks)) = pure $ EProject !(quote env t) (Left ks)
  quote env (VProject t (Right u)) = pure $ EProject !(quote env t) (Right $ !(quote env u))
  quote env (VWith t ks u) = pure $ EWith !(quote env t) ks !(quote env u)
  quote env VPrimVar = Left $ ReadBackError "Can't quote VPrimVar"

||| destruct VPi and VHPi
vAnyPi : Value -> Either Error (Name, Ty, (Value -> Either Error Value))
vAnyPi (VHPi x a b) = Right (x, a, b)
vAnyPi (VPi a b@(MkClosure x _ _)) = Right (x, a, inst b)
vAnyPi t = Left $ Unexpected $ show t ++ " is not a VPi or VHPi"

data Types = TEmpty
           | TBind Types Name Value

axiom : U -> Either Error U
axiom CType = Right Kind
axiom Kind = Right Sort
axiom Sort = Left SortError

rule : U -> U -> U
rule CType CType = CType
rule Kind CType = CType
rule Sort CType = CType
rule CType Kind = Kind
rule Kind Kind = Kind
rule Sort Kind = Sort
rule CType Sort = Sort
rule Kind Sort = Sort
rule Sort Sort = Sort

record Cxt where
  constructor MkCxt
  values : Env
  types  : Types

export
initCxt : Cxt
initCxt = MkCxt Empty TEmpty

envNames : Env -> List Name
envNames Empty = []
envNames (Skip env x) = x :: envNames env
envNames (Extend env x _) = x :: envNames env

||| Extend context with a name, its type, and its value
define : Name -> Value -> Ty -> Cxt -> Cxt
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
      _        => Left $ ErrorMessage "Not a Type/Kind/Sort" -- TODO Better error message

  ||| returns the original `Expr Void` on success
  export
  check : Cxt -> Expr Void -> Value -> Either Error (Expr Void)
  check cxt (EConst CType) vKype = pure $ EConst CType
  check cxt (EConst Kind) vSort = pure $ EConst Kind
  check cxt (EConst Sort) z = Left $ SortError
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

  unexpected : String -> Value -> Either Error a
  unexpected str v = Left (Unexpected $ str ++ " Value: " ++ show v)

  natFoldTy : Value
  natFoldTy =
    VHPi "natural" vType $ \natural =>
    pure $ VHPi "succ" (vFun natural natural) $ \succ =>
    pure $ VHPi "zero" natural $ \zero =>
    pure $ natural

  listFoldTy : Value -> Value
  listFoldTy a =
    VHPi "list" vType $ \list =>
    pure $ VHPi "cons" (vFun a $ vFun list list) $ \cons =>
    pure $ VHPi "nil" list $ \nil =>
    pure $ list

  ||| returns a pair (Expr, Value), which is original Expr, and it's type as a Value
  export
  infer : Cxt -> Expr Void -> Either Error (Expr Void, Value)
  infer cxt (EConst k) = (\k' => (EConst k, VConst k')) <$> axiom k
  infer cxt (EVar x i) = go (types cxt) i
  where
    go : Types -> Int -> Either Error (Expr Void, Value)
    go TEmpty i = Left $ MissingVar $ x -- TODO better error message
    go (TBind ts x' a) i =
      case x == x' of
           True => if i == 0 then Right (EVar x i, a) else go ts (i - 1)
           False => go ts i
  infer cxt (ELam x a t) = do
    (a, ak) <- checkTy cxt a
    av <- eval (values cxt) a
    (t, b) <- infer (bind x av cxt) t
    nb <- quote (x :: (envNames (values cxt))) b
    Right ( ELam x a t
          , VHPi x av $
            \u => Right $ !(eval (Extend (values cxt) x u) nb)) -- TODO check i'm using values right
  infer cxt (EPi x a b) = do
    (a, ak) <- checkTy cxt a
    av <- eval (values cxt) a
    (b, bk) <- checkTy (bind x av cxt) b
    Right (EPi x a b, VConst $ rule ak bk)
  infer cxt (EApp t u) = do
    (t, tt) <- infer cxt t
    (x, a, b) <- vAnyPi tt
    check cxt u a
    Right $ (EApp t u, !(b !(eval (values cxt) u)))
  infer cxt (ELet x Nothing a b) = do
    (a, aa) <- infer cxt a
    v <- eval (values cxt) a
    infer (define x v aa cxt) b
  infer cxt (ELet x (Just t) a b) = do
    tt <- eval (values cxt) t
    check cxt a tt
    v <- eval (values cxt) a
    infer (define x v tt cxt) b
  infer cxt (EAnnot x t) = do
    tv <- eval (values cxt) t
    check cxt x tv
    Right $ (EAnnot x t, tv)
  infer cxt EBool = Right $ (EBool, VConst CType)
  infer cxt (EBoolLit x) = Right $ (EBoolLit x, VBool)
  infer cxt (EBoolAnd x y) = do
    check cxt x VBool
    check cxt y VBool
    Right $ (EBoolAnd x y, VBool)
  infer cxt (EBoolOr x y) = do
    check cxt x VBool
    check cxt y VBool
    Right $ (EBoolOr x y, VBool)
  infer cxt (EBoolEQ x y) = do
    check cxt x VBool
    check cxt y VBool
    Right $ (EBoolEQ x y, VBool)
  infer cxt (EBoolNE x y) = do
    check cxt x VBool
    check cxt y VBool
    Right $ (EBoolNE x y, VBool)
  infer cxt (EBoolIf b t f) = do
    check cxt b VBool
    (t, tt) <- infer cxt t
    check cxt f tt
    Right $ (EBoolIf b t f, tt)
  infer cxt ENatural = Right $ (ENatural, VConst CType)
  infer cxt (ENaturalLit k) = Right $ (ENaturalLit k, VNatural)
  infer cxt ENaturalBuild = pure (ENaturalBuild, vFun natFoldTy VNatural)
  infer cxt ENaturalFold = pure (ENaturalFold, vFun VNatural natFoldTy)
  infer cxt ENaturalIsZero = Right $ (ENaturalIsZero, (vFun VNatural VBool))
  infer cxt ENaturalEven = Right $ (ENaturalEven, (vFun VNatural VBool))
  infer cxt ENaturalOdd = Right $ (ENaturalOdd, (vFun VNatural VBool))
  infer cxt ENaturalSubtract = Right $ (ENaturalOdd, (vFun VNatural (vFun VNatural VNatural)))
  infer cxt ENaturalToInteger = Right $ (ENaturalToInteger, (vFun VNatural VInteger))
  infer cxt ENaturalShow = Right $ (ENaturalShow, (vFun VNatural VText))
  infer cxt (ENaturalPlus t u) = do
    check cxt t VNatural
    check cxt u VNatural
    Right $ (ENaturalPlus t u, VNatural)
  infer cxt (ENaturalTimes t u) = do
    check cxt t VNatural
    check cxt u VNatural
    Right $ (ENaturalTimes t u, VNatural)
  infer cxt EInteger = Right $ (EInteger, VConst CType)
  infer cxt (EIntegerLit x) = Right $ (EIntegerLit x, VInteger)
  infer cxt EIntegerShow = Right $ (EIntegerShow, (vFun VInteger VText))
  infer cxt EIntegerNegate = Right $ (EIntegerNegate, (vFun VInteger VInteger))
  infer cxt EIntegerClamp = Right $ (EIntegerNegate, (vFun VInteger VNatural))
  infer cxt EIntegerToDouble = Right $ (EIntegerNegate, (vFun VInteger VDouble))
  infer cxt EDouble = Right $ (EDouble, VConst CType)
  infer cxt (EDoubleLit x) = Right $ (EDoubleLit x, VDouble)
  infer cxt EDoubleShow = Right $ (EDoubleShow, (vFun VDouble VText))
  infer cxt EText = Right $ (EText, VConst CType)
  infer cxt (ETextLit (MkChunks xs x)) =
    let go = mapChunks (\e => check cxt e VText) in do
    traverse go xs
    Right $ (ETextLit (MkChunks xs x), VText)
  infer cxt (ETextAppend t u) = do
    check cxt t VText
    check cxt u VText
    pure $ (ETextAppend t u, VText)
  infer cxt ETextShow = pure $ (EIntegerShow, (vFun VText VText))
  infer cxt ETextReplace =
    pure ( ETextReplace,
           VHPi "needle" VText $ \needle =>
           pure $ VHPi "replacement" VText $ \replacement =>
           pure $ VHPi "haystack" VText $ \haystack =>
           pure VText)
  infer cxt EList = do
    Right $ (EList, VHPi "a" vType $ \a => Right $ vType)
  infer cxt (EListLit Nothing []) = do
    Left $ ErrorMessage "Not type for list" -- TODO better error message
  infer cxt (EListLit Nothing (x :: xs)) = do
    (x', ty) <- infer cxt x
    traverse (\e => check cxt e ty) xs
    Right $ (EListLit Nothing (x :: xs), VList ty)
  infer cxt (EListLit (Just x) xs) = do
    ty <- eval (values cxt) x
    traverse (\e => check cxt e ty) xs
    Right $ (EListLit (Just x) xs, ty)
  infer cxt (EListAppend t u) = do
    (t', tt) <- infer cxt t
    case tt of
         (VList x) => do
           check cxt u tt
           Right $ (EListAppend t u, tt)
         _ => Left $ ListAppendError "not a list" -- TODO better error message
  infer cxt EListBuild =
    pure (EListBuild, VHPi "a" vType $ \a => pure $ vFun (listFoldTy a) (VList a))
  infer cxt EListFold =
    pure (EListFold, VHPi "a" vType $ \a => pure $ vFun (VList a) (listFoldTy a))
  infer cxt EListLength =
    pure (EListLength, VHPi "a" vType $ \a => pure $ vFun (VList a) VNatural)
  infer cxt EListHead =
    pure (EListHead, VHPi "a" vType $ \a => pure $ vFun (VList a) (VOptional a))
  infer cxt EListLast =
    pure (EListLast, VHPi "a" vType $ \a => pure $ vFun (VList a) (VOptional a))
  infer cxt EListIndexed =
    pure (EListIndexed
         , VHPi "a" vType $ \a =>
           pure $ vFun (VList a)
                  (VList (VRecord (fromList [(MkFieldName "index", VNatural), (MkFieldName "value", a)]))))
  infer cxt EListReverse =
    pure (EListReverse, VHPi "a" vType $ \a => pure $ vFun (VList a) (VList a))
  infer cxt EOptional =
    Right $ (EOptional, VHPi "a" vType $ \a => Right $ vType)
  infer cxt (ESome t) = do
    (t, tt) <- infer cxt t
    check cxt !(quote (envNames $ values cxt) tt) vType -- TODO abstract this out?
    pure (ESome t, VOptional tt)
  infer cxt ENone =
    Right $ (ENone, VHPi "a" vType $ \a => Right $ (VOptional a))
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
  infer cxt (EAssert _) = Left $ AssertError "not an EEquivalent type" -- TODO better error message
  infer cxt (ERecord x) = do
    xs' <- traverse (inferSkip cxt) x
    Right $ (ERecord x, VConst (getHighestType xs'))
  infer cxt (ERecordLit x) = do
    xs' <- traverse (inferSkip cxt) x
    Right $ (ERecordLit x, VRecord xs')
  infer cxt (EUnion x) = do
    xs' <- traverse (mapMaybe (inferSkip cxt)) x
    Right $ (EUnion x, VConst (getHighestTypeM xs'))
  infer cxt (ECombine t u) = do
    (t, tt) <- infer cxt t
    (u, uu) <- infer cxt u
    case (tt, uu) of
         (VRecord a', VRecord b') => do
           ty <- mergeWithApp doCombine a' b'
           Right $ (ECombine t u, VRecord ty)
         (VRecord _, other) => unexpected "Not a RecordLit" other
         (other, _) => unexpected "Not a RecordLit" other
  infer cxt (ECombineTypes a b) = do -- TODO lot of traversals here
    av <- eval (values cxt) a
    bv <- eval (values cxt) b
    case (av, bv) of
         (VRecord a', VRecord b') => do
           ty <- mergeWithApp doCombine a' b'
           Right $ (ECombineTypes a b, snd !(infer cxt !(quote (envNames $ values cxt) (VRecord ty))))
         (other, _) => unexpected "Not a Record" other
  infer cxt (EPrefer t u) = do
    (t, tt) <- infer cxt t
    (u, uu) <- infer cxt u
    case (tt, uu) of
         (VRecord a', VRecord b') => do
           ty <- mergeWithApp' doCombine a' b'
           Right $ (EPrefer t u, VRecord ty)
         (VRecord _, other) => unexpected "Not a RecordLit" other
         (other, _) => unexpected "Not a RecordLit" other
  infer cxt (EMerge t u a) = do
    (u, ut) <- infer cxt u
    (t, tt) <- infer cxt t
    case (ut, tt) of
         (VUnion ts, VRecord us) => do
           case a of
                Nothing => do
                  pure (EMerge t u a, !(inferMerge cxt ts us Nothing))
                (Just a') => do
                  av <- eval (values cxt) a'
                  ty <- inferMerge cxt ts us (Just av)
                  conv (values cxt) av ty
                  pure (EMerge t u a, av)
         (VOptional a', VRecord us) =>
           let newUnion = SortedMap.fromList $
                            [(MkFieldName "None", Nothing), (MkFieldName "Some", Just a')]
           in pure (EMerge t u a, !(inferMerge cxt newUnion us Nothing))
         (other, VRecord _) => unexpected "Not a RecordLit or Optional" other
         (_, other) => unexpected "Not a RecordLit" other
  infer cxt (EToMap t Nothing) = do
    (t, tt) <- infer cxt t
    case tt of
         (VRecord ms) =>
           let xs = SortedMap.toList ms in
           case xs of
                ((k, v) :: ys) => do
                  unify cxt !(inferSkip cxt !(quote (envNames $ values cxt) v)) (VConst CType)
                  foldlM (\x,y => unify cxt x y *> pure x) v (map snd ys)
                  pure (EToMap t Nothing, toMapTy v)
                [] => Left $ ToMapEmpty "Needs an annotation"
         other => unexpected "Not a RecordLit" other
  infer cxt (EToMap t (Just a)) = do
    (t, tt) <- infer cxt (EToMap t Nothing)
    av <- eval (values cxt) a
    unify cxt tt av
    pure (EToMap t (Just a), av)
  infer cxt (EField t@(EUnion x) k) = do
    xv <- traverse (mapMaybe (eval (values cxt))) x
    case lookup k xv of
         Nothing => Left $ FieldNotFoundError $ show k
         (Just Nothing) => Right $ (EField t k, VUnion xv)
         (Just (Just y)) => Right $ (EField t k, (vFun y (VUnion xv)))
  infer cxt (EField (ERecordLit m) k) = do
    case lookup k m of
         Nothing => Left $ FieldNotFoundError $ show k
         (Just x) => infer cxt x
  infer cxt (EField t k) = Left (InvalidFieldType (show t))
  infer cxt (ERecordCompletion t u) = do
    (t, tt) <- infer cxt t
    case tt of
         (VRecord ms) => do
           -- guard $ mapErr "Type" (go (MkFieldName "Type") ms)
           -- guard $ mapErr "default" (go (MkFieldName "default") ms)
           case (lookup (MkFieldName "Type") ms, lookup (MkFieldName "default") ms) of
                (Just x, Just y) =>
                  infer cxt (EAnnot (EPrefer (EField t (MkFieldName "default")) u) (EField t (MkFieldName "Type")))
                (other, (Just _)) => Left $ InvalidRecordCompletion "Type"
                (_, other) => Left $ InvalidRecordCompletion "default"
         other => unexpected "Not a RecordLit" other
  infer cxt (EProject t (Left ks)) = do
    (t, tt) <- infer cxt t
    case tt of
         (VRecord ms) =>
           pure (EProject t (Left ks), VRecord $ fromList !(vProjectByFields ms ks))
         (other) => unexpected "Not a RecordLit" other
  infer cxt (EProject t (Right a)) = do
    (t, tt) <- infer cxt t
    av <- eval (values cxt) a
    case (tt, av) of
         (VRecord ms, VRecord ms') => do
           pure (EProject t (Right a), VRecord $ fromList !(vProjectByFields ms (keys ms')))
         (other, VRecord _) => unexpected "Not a RecordLit" other
         (_, other) => unexpected "Not a Record" other
  infer cxt (EWith t ks u) = do -- TODO understand this
    (t, tt) <- infer cxt t
    pure (EWith t ks u, !(inferWith tt ks u))
  where
    inferWith : Value -> List1 FieldName -> Expr Void -> Either Error Value
    inferWith (VRecord ms) ks y =
      case ks of
           (head ::: []) => do
             (u, uu) <- infer cxt u
             pure $ VRecord $ insert head uu ms
           (head ::: (k :: ks)) => do
             let v = case lookup head ms of
                      Nothing => VRecord (fromList [])
                      (Just v) => v
             v' <- inferWith v (k ::: ks) y
             pure $ VRecord $ insert head v' ms
    inferWith other _ _ = unexpected "Not a RecordLit" other
  infer cxt (EEmbed (Raw x)) = absurd x
  infer cxt (EEmbed (Resolved x)) = infer initCxt x

  toMapTy : Value -> Value
  toMapTy v = VList $ VRecord $ fromList [(MkFieldName "mapKey", VText), (MkFieldName "mapValue", v)]

  checkEmptyMerge : Maybe Value -> Either Error Value
  checkEmptyMerge Nothing = Left $ EmptyMerge "Needs a type annotation"
  checkEmptyMerge (Just v) = pure v

  inferMerge : Cxt
             -> SortedMap FieldName (Maybe Value)
             -> SortedMap FieldName Value
             -> Maybe Value
             -> Either Error Value
  inferMerge cxt us rs mv = do
    xs <- inferUnionHandlers (toList us) (toList rs)
    case Data.List1.fromList xs of
         Nothing => checkEmptyMerge mv
         (Just (head ::: tail)) =>
           foldlM (\acc,v => unify cxt acc v *> pure acc) head tail
  where
    checkKeys : FieldName -> FieldName -> Either Error ()
    checkKeys k k' = case k == k' of
                          True => pure ()
                          False => Left $ MergeUnhandledCase $ show k

    -- Check there's a 1 to 1 relation between union and handlers.  Relying on
    -- calling this with lists create by `SortedMap.toList` Returns a list of
    -- the types when each handler is applied to the corresponding union
    -- alternative.
    inferUnionHandlers : List (FieldName, (Maybe Value))
                        -> List (FieldName, Value)
                        -> Either Error (List (Value))
    inferUnionHandlers [] [] = pure []
    inferUnionHandlers [] ((k, v) :: xs) = Left $ MergeUnusedHandler $ show k
    inferUnionHandlers ((k, v) :: xs) [] = Left $ MergeUnhandledCase $ show k
    inferUnionHandlers ((k, Just v) :: xs) ((k', v') :: ys) = do
      -- if it's an Union field with a value, apply the Record function
      checkKeys k k'
      (_, a', b) <- vAnyPi v'
      unify cxt v a'
      pure $ !(b v) :: !(inferUnionHandlers xs ys)
    inferUnionHandlers ((k, Nothing) :: xs) ((k', v') :: ys) = do
      -- if it's an Union field without value, return the Record value
      checkKeys k k'
      pure $ v' :: !(inferUnionHandlers xs ys)

  ||| infer but only return `Value`, not `(Expr Void, Value)`
  inferSkip : Cxt -> Expr Void -> Either Error Value
  inferSkip cxt = (\e => Right $ snd !(infer cxt e))

  pickHigherType : (acc : U) -> Ty -> U
  pickHigherType CType (VConst Kind) = Kind
  pickHigherType _ (VConst Sort) = Sort
  pickHigherType acc other = acc

  getHighestTypeM : Foldable t => t (Maybe Value) -> U
  getHighestTypeM x = foldl go CType x
  where
    go : U -> Maybe Value -> U
    go x Nothing = x
    go x (Just y) = pickHigherType x y

  export
  getHighestType : Foldable t => t Value -> U
  getHighestType x = foldl pickHigherType CType x
