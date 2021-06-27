module Idrall.Eval

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
export
vType : Value
vType = VConst CType

||| returns `VConst Kind`
export
vKind : Value
vKind = VConst Kind

||| returns `VConst Sort`
export
vSort : Value
vSort = VConst Sort

-- evaluator
mutual
  export
  inst : Closure -> Value -> Either Error Value
  inst = evalClosure

  export
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
                 VPrimVar => pure $ VNaturalBuild VPrimVar
                 t => vAppM t [ VNatural
                              , VHLam (Typed "n" VNatural) $ \n =>
                                    pure $ vNaturalPlus n (VNaturalLit 1)
                              , VNaturalLit 0
                              ]
  eval env ENaturalFold =
    pure $ VPrim $ \n =>
    pure $ VPrim $ \natural =>
    pure $ VPrim $ \succ =>
    pure $ VPrim $ \zero =>
    let inert = VNaturalFold n natural succ zero
    in case zero of
            VPrimVar => pure inert
            _ => case succ of
                      VPrimVar => pure inert
                      _ => case natural of
                                VPrimVar => pure inert
                                _ => case n of
                                          VNaturalLit n' =>
                                              go succ zero n'
                                          _ => pure inert
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
    pure $ VPrim $
      \x => case x of
                 VNaturalLit 0 => pure $ VHLam NaturalSubtractZero (\y => pure y)
                 x'@(VNaturalLit m) => pure $ VPrim $
                      \y => case y of
                                 -- unintuitive order for `minus`, but this is correct
                                 (VNaturalLit n) => pure $ VNaturalLit (minus n m)
                                 y' => pure $ VNaturalSubtract x' y'
                 x' => pure $ VPrim $
                      \y => case y of
                                 (VNaturalLit 0) => pure $ VNaturalLit 0
                                 y' => case conv env x' y' of
                                            (Right _) => pure $ VNaturalLit 0
                                            (Left _) => pure $ VNaturalSubtract x' y'
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
         (VNaturalLit 0, u) => pure $ VNaturalLit 0
         (VNaturalLit 1, u) => pure u
         (t, VNaturalLit 1) => pure t
         (t, VNaturalLit 0) => pure $ VNaturalLit 0
         (VNaturalLit t, VNaturalLit u) => pure (VNaturalLit $ t * u)
         (t, u) => pure $ VNaturalTimes t u
  eval env EInteger = Right VInteger
  eval env (EIntegerLit k) = Right (VIntegerLit k)
  eval env EIntegerShow =
    Right $ VPrim $
      \c => case c of
                 VIntegerLit n => case n >= 0 of
                                       True => pure $ VTextLit (MkVChunks [] ("+" ++ (show n)))
                                       False => pure $ VTextLit (MkVChunks [] (show n))
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
                   VPrimVar => pure $ VListBuild a VPrimVar
                   t => vAppM t [ VList a
                                , VHLam (Typed "a" a) $ \x =>
                                    pure $ VHLam (Typed "as" (VList a)) $ \as =>
                                      vListAppend (VListLit Nothing [x]) as
                                , VListLit (Just a) []
                                ]
  eval env EListFold =
    pure $ VPrim $ \a =>
    pure $ VPrim $ \as =>
    pure $ VPrim $ \list =>
    pure $ VPrim $ \cons =>
    pure $ VPrim $ \nil =>
      let inert = pure $ VListFold a as list cons nil in
        case nil of
        VPrimVar => inert
        _ => case cons of
            VPrimVar => inert
            _ => case list of
                VPrimVar => inert
                _ => case a of
                    VPrimVar => inert
                    _ => case as of
                        VListLit _ as' =>
                           foldrM (\x,b => vAppM cons [x, b]) nil as'
                        _ => inert
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
  eval env (EField x k) =
    case !(eval env x) of
         VRecordLit m =>
            case lookup k m of
                 (Just v) => pure v
                 Nothing => Left (FieldNotFoundError $ show k)
         VUnion m =>
            case lookup k m of
                 (Just (Just y)) => pure $ VPrim $ \u => pure $ VInject m k (Just u)
                 (Just Nothing) => pure $ VInject m k Nothing
                 Nothing => Left (FieldNotFoundError $ show k)
         t => pure $ VField t k
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
  eval env (EImportAlt x y) = eval env x
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

  export
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
        in VListLit (listIndexedType a) (reverse final) -- TODO hacky reverse
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

  export
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

  export
  strFromExpr : Expr Void -> Maybe String
  strFromExpr (ETextLit (MkChunks [] x)) = pure x
  strFromExpr (ETextLit (MkChunks (start :: xs) end)) =
    let mid = traverse go xs in
    pure $ !(go start) ++ (foldl (<+>) "" !mid) ++ end
  where
    go : (String, Expr Void) -> Maybe String
    go (x, e) = pure $ x ++ !(strFromExpr e)
  strFromExpr _ = Nothing

  export
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

  export
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
