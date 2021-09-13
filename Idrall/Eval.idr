module Idrall.Eval

import Idrall.Expr
import Idrall.Error
import Idrall.Value
import Idrall.Map

import Data.List
import Data.List1
import Data.String

-- alpha equivalence
nestError : Either Error b -> Error -> Either Error b
nestError x e =
  case x of
       (Left e') => Left $ NestedError initFC e e'
       (Right x') => pure x'

||| returns `VConst CType`
export
vType : Value
vType = VConst initFC CType

||| returns `VConst Kind`
export
vKind : Value
vKind = VConst initFC Kind

||| returns `VConst Sort`
export
vSort : Value
vSort = VConst initFC Sort

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

  evalVar : FC -> Env -> Name -> Int -> Either Error Value
  evalVar fc Empty x i = pure $ VVar fc x (0 - i - 1)
  evalVar fc (Skip env x') x i =
    case x == x' of
         True => if i == 0 then pure $ VVar fc x (countName x env) else evalVar fc env x (i - 1)
         False => evalVar fc env x i
  evalVar fc (Extend env x' v) x i =
    case x == x' of
         True => if i == 0 then pure v else evalVar fc env x (i - 1)
         False => evalVar fc env x i

{-
  vVar : FC -> Env -> Name -> Int -> Either Error Value
  vVar = evalVar
  -}

  export
  covering
  eval : Env -> Expr Void -> Either Error Value
  eval env (EConst fc x) = pure (VConst fc x)
  eval env (EVar fc x i)
    = evalVar fc env x i
  eval env (ELam fc x ty body)
    = do vTy <- eval env ty
         pure (VLambda fc vTy (MkClosure x env body))
  eval env (EPi fc x dom ran)
    = do ty <- eval env dom
         pure (VPi fc ty (MkClosure x env ran))
  eval env (EApp fc rator rand)
    = do rator' <- eval env rator
         rand' <- eval env rand
         doApply rator' rand'
  eval env (ELet fc x _ r e) =
    do vr <- eval env r
       eval (Extend env x vr) e
  eval env (EAnnot fc x _) = eval env x
  eval env (EBool fc) = pure $ VBool fc
  eval env (EBoolLit fc b) = pure $ VBoolLit fc b
  eval env (EBoolAnd fc t u) =
    case (!(eval env t), !(eval env u)) of
         (VBoolLit _ True, u) => pure u
         (VBoolLit _ False, u) => pure $ VBoolLit fc False
         (t, VBoolLit _ True) => pure t
         (t, VBoolLit _ False) => pure $ VBoolLit fc False
         (t, u) => case conv env t u of
                        Right _ => pure t
                        Left _ => pure $ VBoolAnd fc t u
  eval env (EBoolOr fc t u) =
    case (!(eval env t), !(eval env u)) of
         (VBoolLit _ False, u) => pure u
         (VBoolLit _ True, u) => pure $ VBoolLit fc True
         (t, VBoolLit _ False) => pure t
         (t, VBoolLit _ True) => pure $ VBoolLit fc True
         (t, u) => case conv env t u of
                        Right _ => pure t
                        Left _ => pure $ VBoolOr fc t u
  eval env (EBoolEQ fc t u) =
    case (!(eval env t), !(eval env u)) of
         (VBoolLit _ True, u) => pure u
         (t, VBoolLit _ True) => pure t
         (t, u) => case conv env t u of
                        Right _ => pure $ VBoolLit fc True
                        Left _ => pure $ VBoolEQ fc t u
  eval env (EBoolNE fc t u) =
    case (!(eval env t), !(eval env u)) of
         (VBoolLit _ False, u) => pure u
         (t, VBoolLit _ False) => pure t
         (t, u) => case conv env t u of
                        Right _ => pure $ VBoolLit fc False
                        Left _ => pure $ VBoolNE fc t u
  eval env (ENatural fc) = pure $ VNatural fc
  eval env (ENaturalLit fc k) = pure $ VNaturalLit fc k
  eval env (ENaturalBuild fc) =
    pure $ VPrim $
      \c => case c of
                 VPrimVar fc => pure $ VNaturalBuild fc $ VPrimVar fc
                 t => vAppM t [ VNatural fc
                              , VHLam fc (Typed "n" $ VNatural fc) $ \n =>
                                    pure $ vNaturalPlus fc n (VNaturalLit fc 1)
                              , VNaturalLit fc 0
                              ]
  eval env (ENaturalFold fc) =
    pure $ VPrim $ \n =>
    pure $ VPrim $ \natural =>
    pure $ VPrim $ \succ =>
    pure $ VPrim $ \zero =>
    let inert = VNaturalFold initFC n natural succ zero
    in case zero of
            VPrimVar fc => pure inert
            _ => case succ of
                      VPrimVar fc => pure inert
                      _ => case natural of
                                VPrimVar fc => pure inert
                                _ => case n of
                                          VNaturalLit fc' n' =>
                                              go succ zero n'
                                          _ => pure inert
  where
    go : Value -> Value -> Nat -> Either Error Value
    go succ acc 0 = pure acc
    go succ acc (S k) = go succ !(vApp succ acc) k
  eval env (ENaturalIsZero fc) =
     pure $ VPrim $
       \c => case c of
                  VNaturalLit fc' n => pure $ VBoolLit fc' (n == 0)
                  n             => pure $ VNaturalIsZero fc n
  eval env (EBoolIf fc b t f) =
    case (!(eval env b), !(eval env t), !(eval env f)) of
         (VBoolLit _ True, t, f) => pure t
         (VBoolLit _ False, t, f) => pure f
         (b, VBoolLit _ True, VBoolLit _ False) => pure b
         (b, t, f) => case conv env t f of
                           (Right _) => pure t
                           (Left _) => pure $ VBoolIf fc b t f
  eval env (ENaturalEven fc) =
    pure $ VPrim $
      \c => case c of
                 VNaturalLit fc n => pure $ VBoolLit fc (isEven n)
                 n             => pure $ VNaturalEven fc n
  eval env (ENaturalOdd fc) =
    pure $ VPrim $
      \c => case c of
                 VNaturalLit fc n => pure $ VBoolLit fc (isOdd n)
                 n             => pure $ VNaturalOdd fc n
  eval env (ENaturalSubtract fc) = do
    pure $ VPrim $
      \x => case x of
                 VNaturalLit fc 0 => pure $ VHLam fc NaturalSubtractZero (\y => pure y)
                 x'@(VNaturalLit fc m) => pure $ VPrim $
                      \y => case y of
                                 -- unintuitive order for `minus`, but this is correct
                                 (VNaturalLit fc n) => pure $ VNaturalLit fc (minus n m)
                                 y' => pure $ VNaturalSubtract fc x' y'
                 x' => pure $ VPrim $
                      \y => case y of
                                 (VNaturalLit fc 0) => pure $ VNaturalLit fc 0
                                 y' => case conv env x' y' of
                                            (Right _) => pure $ VNaturalLit fc 0
                                            (Left _) => pure $ VNaturalSubtract fc x' y'
  eval env (ENaturalShow fc) =
    pure $ VPrim $
      \c => case c of
                 VNaturalLit fc n => pure $ VTextLit fc (MkVChunks [] (show n))
                 n             => pure $ VNaturalShow fc n
  eval env (ENaturalToInteger fc) =
    pure $ VPrim $
      \c => case c of
                 VNaturalLit fc n => pure $ VIntegerLit fc (cast n)
                 n             => pure $ VNaturalToInteger fc n
  eval env (ENaturalPlus fc t u) = pure $ vNaturalPlus fc !(eval env t) !(eval env u)
  eval env (ENaturalTimes fc t u) =
    case (!(eval env t), !(eval env u)) of
         (VNaturalLit _ 0, u) => pure $ VNaturalLit fc 0
         (VNaturalLit _ 1, u) => pure u
         (t, VNaturalLit _ 1) => pure t
         (t, VNaturalLit _ 0) => pure $ VNaturalLit fc 0
         (VNaturalLit _ t, VNaturalLit _ u) => pure (VNaturalLit fc $ t * u)
         (t, u) => pure $ VNaturalTimes fc t u
  eval env (EInteger fc) = pure $ VInteger fc
  eval env (EIntegerLit fc k) = pure (VIntegerLit fc k)
  eval env (EIntegerShow fc) =
    pure $ VPrim $
      \c => case c of
                 VIntegerLit fc n => case n >= 0 of
                                       True => pure $ VTextLit fc (MkVChunks [] ("+" ++ (show n)))
                                       False => pure $ VTextLit fc (MkVChunks [] (show n))
                 n             => pure $ VIntegerShow fc n
  eval env (EIntegerNegate fc) = pure $ VPrim $
                            \c => case c of
                                       VIntegerLit fc n => pure $ VIntegerLit fc (negate n)
                                       n             => pure $ VIntegerNegate fc n
  eval env (EIntegerClamp fc) =
    pure $ VPrim $
      \c => case c of
                 VIntegerLit fc n => pure $ VNaturalLit fc (integerToNat n)
                 n             => pure $ VIntegerClamp fc n
  eval env (EIntegerToDouble fc) =
    pure $ VPrim $
      \c => case c of
                 VIntegerLit fc n => pure $ VDoubleLit fc (cast n)
                 n             => pure $ VIntegerToDouble fc n
  eval env (EDouble fc) = pure $ VDouble fc
  eval env (EDoubleLit fc k) = pure (VDoubleLit fc k)
  eval env (EDoubleShow fc) =
    pure $ VPrim $
      \c => case c of
                 VDoubleLit fc n => pure $ VTextLit fc (MkVChunks [] (show n))
                 n             => pure $ VDoubleShow fc n
  eval env (EText fc) = pure $ VText fc
  eval env (ETextLit fc (MkChunks xs x)) = do
    xs' <- traverse (mapChunks (eval env)) xs
    pure (VTextLit fc (MkVChunks xs' x))
  eval env (ETextAppend fc x y) =
    case (!(eval env x), !(eval env y)) of
         (VTextLit fc (MkVChunks [] ""), u) => pure u
         (t, VTextLit fc (MkVChunks [] "")) => pure t
         (VTextLit fc x, VTextLit fc' y) => pure $ VTextLit fc (x <+> y)
         (t, u) => pure $ VTextAppend fc t u
  eval env (ETextShow fc) =
    pure $ VPrim $ \c =>
      case c of
           VTextLit fc (MkVChunks [] x) => pure $ VTextLit fc (MkVChunks [] (vTextShow x))
           t => pure $ VTextShow fc t
  eval env (ETextReplace fc) = -- Probably not right
    pure $ VPrim $
      \needle => pure $ VPrim $
        \replacement => pure $ VPrim $
          \haystack =>
            case needle of
                 VTextLit fc (MkVChunks [] "") => pure haystack
                 VTextLit fc (MkVChunks [] needleText) =>
                   case haystack of
                        (VTextLit fc (MkVChunks [] haystackText)) =>
                          case replacement of
                               (VTextLit fc (MkVChunks [] replacementText)) =>
                                 pure $ VTextLit fc $
                                        MkVChunks [] $ textReplace needleText replacementText haystackText
                               (VTextLit fc (MkVChunks chx replacementText)) =>
                                 case strFromChunks chx  of
                                      Nothing => Left $ ErrorMessage fc "could not make string for replacement"
                                      (Just str) =>
                                         pure $ VTextLit fc $
                                         MkVChunks [] $ textReplace
                                                          needleText
                                                          replacementText
                                                          haystackText
                               _ => pure $ VTextReplace fc needle replacement haystack
                        _ => pure $ VTextReplace fc needle replacement haystack
                 k => pure $ VTextReplace fc needle replacement haystack
  eval env (EList fc) = do
    pure $ VPrim $ \a => pure $ VList fc a
  eval env (EListLit fc Nothing es) = do
    vs <- mapListEither es (eval env)
    pure (VListLit fc Nothing vs)
  eval env (EListLit fc (Just ty) es) = do
    ty' <- eval env ty
    vs <- mapListEither es (eval env)
    pure (VListLit fc (Just ty') vs)
  eval env (EListAppend fc x y) = do
    x' <- eval env x
    y' <- eval env y
    vListAppend fc x' y'
  eval env (EListBuild fc) =
    pure $ VPrim $
      \a => pure $ VPrim $
        \c => case c of
                   VPrimVar fc => pure $ VListBuild fc a $ VPrimVar fc
                   t => vAppM t [ VList fc a
                                , VHLam fc (Typed "a" a) $ \x =>
                                    pure $ VHLam fc (Typed "as" (VList fc a)) $ \as =>
                                      vListAppend fc (VListLit fc Nothing [x]) as
                                , VListLit fc (Just a) []
                                ]
  eval env (EListFold fc) =
    pure $ VPrim $ \a =>
    pure $ VPrim $ \as =>
    pure $ VPrim $ \list =>
    pure $ VPrim $ \cons =>
    pure $ VPrim $ \nil =>
      let inert = pure $ VListFold fc a as list cons nil in
        case nil of
        VPrimVar fc => inert
        _ => case cons of
            VPrimVar fc => inert
            _ => case list of
                VPrimVar fc => inert
                _ => case a of
                    VPrimVar fc => inert
                    _ => case as of
                        VListLit fc _ as' =>
                           foldrM (\x,b => vAppM cons [x, b]) nil as'
                        _ => inert
    where
      foldrM : (Foldable t, Monad m) => (funcM: b -> a -> m a) -> (init: a) -> (input: t b) -> m a
      foldrM fm a0 = foldr (\b,ma => ma >>= fm b) (pure a0)
  eval env (EListLength fc) =
    pure $ VPrim $
      \a => pure $ VPrim $
        \c => case c of
                   (VListLit fc _ as) => pure $ VNaturalLit fc (length as)
                   as => pure $ VListLength fc a as
  eval env (EListHead fc) =
    pure $ VPrim $ \a =>
      pure $ VPrim $
             \c => case c of
                        VListLit fc _ [] => pure $ VNone fc a
                        VListLit fc _ (h :: _) => pure $ VSome fc h
                        as => pure $ VListHead fc a as
  eval env (EListLast fc) =
    pure $ VPrim $
      \a => pure $ VPrim $
        \c => case c of
                   VListLit fc _ as =>
                     case last' as of
                          Nothing => pure $ VNone fc a
                          (Just t) => pure $ VSome fc t
                   as => pure $ VListLast fc a as
  eval env (EListIndexed fc) =
    pure $ VPrim $
      \a => pure $ VPrim $
        \c => case c of
                   VListLit fc t as => pure $ vListIndexed fc t as
                   as => pure $ VListLast fc a as
  eval env (EListReverse fc) =
    pure $ VPrim $
      \a => pure $ VPrim $
        \c => case c of
                   VListLit fc t as => pure $ VListLit fc t (reverse as)
                   as => pure $ VListReverse fc a as
  eval env (EOptional fc) = pure $ VPrim $ \a => pure $ VOptional fc a
  eval env (ESome fc a) = pure (VSome fc !(eval env a))
  eval env (ENone fc) = pure $ VPrim $ \a => pure $ VNone fc a
  eval env (EEquivalent fc x y) =
    do xV <- eval env x
       yV <- eval env y
       pure (VEquivalent fc xV yV)
  eval env (EAssert fc x) = do
    xV <- eval env x
    doAssert env xV
  eval env (ERecord fc x) =
    let xs = toList x in
    do xs' <- traverse (mapRecord (eval env)) xs
       pure (VRecord fc (fromList xs'))
  eval env (ERecordLit fc x) =
    let xs = toList x in
    do xs' <- traverse (mapRecord (eval env)) xs
       pure (VRecordLit fc (fromList xs'))
  eval env (ECombine fc x y) = do
    x' <- eval env x
    y' <- eval env y
    doCombine fc x' y'
  eval env (ECombineTypes fc x y) = do
    x' <- eval env x
    y' <- eval env y
    doCombine fc x' y'
  eval env (EPrefer fc x y) = do
    x' <- eval env x
    y' <- eval env y
    doPrefer fc x' y'
  eval env (EMerge fc x y ma) = -- TODO Double check this
    case (!(eval env x), !(eval env y), !(mapMaybe (eval env) ma)) of
         (VRecordLit fc m, VInject fc' _ k (Just t), _) =>
           case lookup k m of
                Just f => vApp f t
                Nothing => Left $ MergeUnhandledCase fc $ show k -- TODO DRY these error conditions
         (VRecordLit fc m, VInject fc' _ k _, _) =>
           case lookup k m of
                Just t => pure t
                Nothing => Left $ MergeUnhandledCase fc $ show k
         (VRecordLit fc m, VSome fc' t, _) =>
           case lookup (MkFieldName "Some") m of
                Just f => vApp f t
                Nothing => Left $ MergeUnhandledCase fc $ "Some"
         (VRecordLit fc m, VNone fc' _, _) =>
           case lookup (MkFieldName "None") m of
                Just t => pure t
                Nothing => Left $ MergeUnhandledCase fc $ "None"
         (t, u, ma) => pure $ VMerge fc t u ma
  eval env (EUnion fc x) =
    let xs = toList x in
    do xs' <- traverse (mapUnion (eval env)) xs
       pure (VUnion fc (fromList xs'))
  eval env (EField fc x k) =
    case !(eval env x) of
         VRecordLit fc m =>
            case lookup k m of
                 (Just v) => pure v
                 Nothing => Left (FieldNotFoundError fc $ show k)
         VUnion fc m =>
            case lookup k m of
                 (Just (Just y)) => pure $ VPrim $ \u => pure $ VInject fc m k (Just u)
                 (Just Nothing) => pure $ VInject fc m k Nothing
                 Nothing => Left (FieldNotFoundError fc $ show k)
         t => pure $ VField fc t k
  eval env (ERecordCompletion fc t u) =
    eval env (EAnnot fc (EPrefer fc (EField fc t (MkFieldName "default")) u) (EField fc t (MkFieldName "Type")))
  eval env (EToMap fc x Nothing) =
    case !(eval env x) of
         VRecordLit fc ms =>
           let xs = SortedMap.toList ms in
               case xs of
                    [] => Left $ ToMapEmpty fc "Needs an annotation"
                    (y :: ys) => pure $ VListLit fc Nothing $ map vToMap (y :: ys)
         other => pure $ VToMap fc other Nothing
  eval env (EToMap fc x (Just y)) = do
    y' <- eval env y
    case !(eval env x) of
         VRecordLit fc ms => pure $ VListLit fc (Just y') $ map vToMap (SortedMap.toList ms)
         other => pure $ VToMap fc other Nothing
  eval env (EProject fc x (Left ks)) =
    case !(eval env x) of
         VRecordLit fc ms => pure $ VRecordLit fc $ fromList !(vProjectByFields fc ms ks)
         other => Left (Unexpected fc $ "Not a RecordLit. Value: " ++ show other)
  eval env (EProject fc x (Right y)) =
    case (!(eval env x), !(eval env y)) of
         (VRecordLit fc ms, VRecordLit fc' ms') => pure $ VRecordLit fc $ fromList !(vProjectByFields fc ms (keys ms'))
         (other, VRecord fc _) => Left (Unexpected fc $ "Not a RecordLit. Value: " ++ show other)
         (_, other) => Left (Unexpected fc $ "Not a Record. Value: " ++ show other)
  eval env (EWith fc x ks y) = vWith fc !(eval env x) ks !(eval env y)
  eval env (EImportAlt fc x y) = eval env x
  eval env (EEmbed fc (Raw x)) = absurd x
  eval env (EEmbed fc (Resolved x)) = eval Empty x

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
  vToMap (MkFieldName k, v) = VRecordLit initFC $ fromList
    [ (MkFieldName "mapKey", VTextLit initFC $ MkVChunks [] k)
    , (MkFieldName "mapValue", v)
    ]

  vWith : FC -> Value -> List1 FieldName -> Value -> Either Error Value
  vWith _ (VRecordLit fc ms) (head ::: []) u = pure $ VRecordLit fc $ insert head u ms
  vWith _ (VRecordLit fc ms) (head ::: (k :: ks)) u =
    case lookup head ms of
         Nothing =>
           let new = VRecordLit fc (fromList [])
               rest = vWith fc new (k ::: ks) u
           in
           pure $ VRecordLit fc $ insert head !rest ms
         (Just u') =>
           let rest = vWith fc u' (k ::: ks) u in
           pure $ VRecordLit fc $ insert head !rest ms
  vWith fc t ks u = pure $ VWith fc t ks u

  export
  vProjectByFields : FC -> SortedMap FieldName Value -> List FieldName -> Either Error (List (FieldName, Value))
  vProjectByFields fc ms ks = traverse (lookupRecord ms) ks
  where
    lookupRecord : SortedMap FieldName Value -> FieldName -> Either Error (FieldName, Value)
    lookupRecord ms k = case lookup k ms of
                             Nothing => Left $ FieldNotFoundError fc $ show k
                             (Just v) => pure (k, v)

  listIndexedType : Maybe Value -> Maybe Value
  listIndexedType Nothing = Nothing
  listIndexedType (Just a) =
    Just $ VRecord initFC (fromList [(MkFieldName "index", VNatural initFC), (MkFieldName "value", a)])

  vNaturalPlus : FC -> Value -> Value -> Value
  vNaturalPlus fc (VNaturalLit _ 0) u = u
  vNaturalPlus fc t (VNaturalLit _ 0) = t
  vNaturalPlus fc (VNaturalLit _ t) (VNaturalLit _ u) = VNaturalLit fc $ t + u
  vNaturalPlus fc t u = VNaturalPlus fc t u

  -- TODO lots of traversals here
  vListIndexed : FC -> Maybe Value -> List Value -> Value
  vListIndexed fc a xs =
    let prep = foldl go [] xs
        lists = map toRecordList prep
        recordsAsLists = map toRecordList prep
        final = map toRecord recordsAsLists
        in VListLit fc (listIndexedType a) (reverse final) -- TODO hacky reverse
  where
    go : List (Nat, Value) -> Value -> List (Nat, Value)
    go [] t = [(0, t)]
    go acc@((i, _) :: _) u = (i+1, u) :: acc
    toRecordList : (Nat, Value) -> List (FieldName, Value)
    toRecordList (i, v) = [(MkFieldName "index", VNaturalLit initFC i), (MkFieldName "value", v)]
    toRecord : List (FieldName, Value) -> Value
    toRecord xs = VRecordLit initFC $ fromList xs

  covering
  doApply : Value -> Value -> Either Error Value
  doApply (VLambda fc ty closure) arg =
    evalClosure closure arg
  doApply (VHLam fc i f) arg = (f arg)
  doApply f arg = pure $ VApp initFC f arg

  vApp : Value -> Value -> Either Error Value
  vApp = doApply

  vAppM : Value -> List Value -> Either Error Value
  vAppM x xs = foldlM vApp x xs

  covering
  doAssert : Env -> Value -> Either Error Value
  doAssert env v@(VEquivalent fc t u) = do
    conv env t u
    pure $ VAssert fc v
  doAssert env x = Left (AssertError (getFC x) ("not an equivalence type: " ++ show x))

  vListAppend : FC -> Value -> Value -> Either Error Value
  vListAppend fc (VListLit fc' _ []) u = pure u
  vListAppend fc t (VListLit fc' _ []) = pure t
  vListAppend fc (VListLit fc' t xs) (VListLit fc'' _ ys) =
    pure (VListLit fc t (xs ++ ys))
  vListAppend fc x y = pure $ VListAppend fc x y

  export
  doCombine : FC -> Value -> Value -> Either Error Value
  doCombine _ (VRecordLit fc x) (VRecordLit fc' y) =
    pure (VRecordLit fc $ !(mergeWithApp (doCombine fc) x y))
  doCombine _ (VRecord fc x) (VRecord fc' y) =
    pure (VRecord fc $ !(mergeWithApp (doCombine fc) x y))
  doCombine fc x y = pure $ VCombineTypes fc x y

  doPrefer : FC -> Value -> Value -> Either Error Value
  doPrefer _ (VRecordLit fc x) (VRecordLit fc' y) =
    pure (VRecordLit fc $ !(mergeWithApp' (doPrefer fc) x y))
  doPrefer fc x y = pure $ VPrefer fc x y

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
  convFresh x env = (x, VVar initFC x (countName x env))

  convFreshCl : Closure -> Env -> (Name, Value, Closure)
  convFreshCl cl@(MkClosure x _ _) env = (x, snd (convFresh x env), cl)

  convErr : (Show x) => FC -> x -> x -> Either Error a
  convErr fc x y = Left $ AlphaEquivError fc $ show x ++ "\n not alpha equivalent to:\n" ++ show y

  export
  strFromExpr : Expr Void -> Maybe String
  strFromExpr (ETextLit fc (MkChunks [] x)) = pure x
  strFromExpr (ETextLit fc (MkChunks (start :: xs) end)) =
    let mid = traverse go xs in
    pure $ !(go start) ++ (foldl (<+>) "" !mid) ++ end
  where
    go : (String, Expr Void) -> Maybe String
    go (x, e) = pure $ x ++ !(strFromExpr e)
  strFromExpr _ = Nothing

  export
  strFromChunks : List (String, Value) -> Maybe String
  strFromChunks [] = Just neutral
  strFromChunks ((str, (VTextLit initFC (MkVChunks xys' y))) :: xs') = do
    rest <- strFromChunks xs'
    mid <- strFromChunks xys'
    Just (str ++ mid ++ y ++ rest)
  strFromChunks ((str, _) :: xs') = Nothing

  convChunks : FC -> Env -> VChunks -> VChunks -> Either Error ()
  convChunks fc env (MkVChunks [] z) (MkVChunks [] z') = convEq fc z z'
  convChunks fc env (MkVChunks ((s, t) :: xys) z) (MkVChunks ((s', t') :: xys') z') = do
    convEq fc s s'
    conv env t t'
    convChunks fc env (MkVChunks xys z) (MkVChunks xys' z')
  convChunks fc env t u = convErr fc t u

  convList : FC -> Env -> List Value -> List Value -> Either Error ()
  convList fc env [] [] = pure ()
  convList fc env (t :: xs) (t' :: xs') = do
    conv env t t'
    convList fc env xs xs'
  convList fc env t u = convErr fc t u

  convUnion : FC -> Env -> List (FieldName, Maybe Value) -> List (FieldName, Maybe Value) -> Either Error ()
  convUnion fc env [] [] = pure ()
  convUnion fc env ((x, Just t) :: xs) ((x', Just t') :: ys) = do
    convEq fc x x'
    conv env t t'
    convUnion fc env xs ys
  convUnion fc env ((x, Nothing) :: xs) ((x', Nothing) :: ys) = do
    convEq fc x x'
    convUnion fc env xs ys
  convUnion fc env t u = convErr fc t u

  convEq : (Eq x, Show x) => FC -> x -> x -> Either Error ()
  convEq fc a b =
    case a == b of
         True => pure ()
         False => convErr fc a b

  convSkip : Env -> Name -> Value -> Value -> Either Error ()
  convSkip env x = conv (Skip env x)

  export
  conv : Env -> Value -> Value -> Either Error ()
  conv env (VLambda fc _ t) (VLambda fc' _ t') =
    let (x, v, t) = convFreshCl t env in do
    convSkip env x !(inst t v) !(inst t' v)
  conv env (VLambda fc _ t) (VHLam fc' _ t') =
    let (x, v, t) = convFreshCl t env in do
    convSkip env x !(inst t v) !(t' v)
  conv env (VLambda fc _ t) t' =
    let (x, v, t) = convFreshCl t env in do
    convSkip env x !(inst t v) !(vApp t' v)
  conv env (VHLam fc _ t) (VLambda fc' _ t') =
    let (x, v, t') = convFreshCl t' env in do
    convSkip env x !(t v) !(inst t' v)
  conv env (VHLam fc _ t) (VHLam fc' _ t') =
    let (x, v) = convFresh "x" env in do
    convSkip env x !(t v) !(t' v)
  conv env (VHLam fc _ t) t' =
    let (x, v) = convFresh "x" env in do
    convSkip env x !(t v) !(vApp t' v)
  conv env t (VLambda fc _ t') =
    let (x, v, t') = convFreshCl t' env in do
    convSkip env x !(vApp t v) !(inst t' v)
  conv env t (VHLam fc _ t') =
    let (x, v) = convFresh "x" env in do
    convSkip env x !(vApp t v) !(t' v)

  conv env (VPi fc a b) (VPi fc' a' b') =
    let (x, v, b') = convFreshCl b' env in do
    conv env a a'
    convSkip env x !(inst b v) !(inst b' v)
  conv env (VPi fc a b) (VHPi fc' x a' b') =
    let (x, v) = convFresh "x" env in do
    conv env a a'
    convSkip env x !(inst b v) !(b' v)
  conv env (VHPi fc _ a b) (VPi fc' a' b') =
    let (x, v, b') = convFreshCl b' env in do
    conv env a a'
    convSkip env x !(b v) !(inst b' v)
  conv env (VHPi fc _ a b) (VHPi fc' x a' b') =
    let (x, v) = convFresh "x" env in do
    conv env a a'
    convSkip env x !(b v) !(b' v)

  conv env (VConst fc k) (VConst fc' k') = convEq fc k k'
  conv env (VVar fc x i) (VVar fc' x' i') = do
    convEq fc x x'
    convEq fc i i'

  conv env (VApp fc t u) (VApp fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VBool fc) (VBool fc') = pure ()
  conv env (VBoolLit fc b) (VBoolLit fc' b') = convEq fc b b'
  conv env (VBoolAnd fc t u) (VBoolAnd fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VBoolOr fc t u) (VBoolOr fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VBoolEQ fc t u) (VBoolEQ fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VBoolNE fc t u) (VBoolNE fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VBoolIf fc b t f) (VBoolIf fc' b' t' f') = do
    conv env b b'
    conv env t t'
    conv env f f'
  conv env (VNatural fc) (VNatural fc') = pure ()
  conv env (VNaturalLit fc k) (VNaturalLit fc' k') = convEq fc k k'
  conv env (VNaturalBuild fc t) (VNaturalBuild fc' t') = conv env t t'
  conv env (VNaturalFold fc t u v w) (VNaturalFold fc' t' u' v' w') = do
    conv env t t'
    conv env u u'
    conv env v v'
    conv env w w'
  conv env (VNaturalIsZero fc t) (VNaturalIsZero fc' t') = conv env t t'
  conv env (VNaturalEven fc t) (VNaturalEven fc' t') = conv env t t'
  conv env (VNaturalOdd fc t) (VNaturalOdd fc' t') = conv env t t'
  conv env (VNaturalShow fc t) (VNaturalShow fc' t') = conv env t t'
  conv env (VNaturalSubtract fc t u) (VNaturalSubtract fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VNaturalToInteger fc t) (VNaturalToInteger fc' t') = conv env t t'
  conv env (VNaturalPlus fc t u) (VNaturalPlus fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VNaturalTimes fc t u) (VNaturalTimes fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VInteger fc) (VInteger fc') = pure ()
  conv env (VIntegerLit fc t) (VIntegerLit fc' t') = convEq fc t t'
  conv env (VIntegerShow fc t) (VIntegerShow fc' t') = conv env t t'
  conv env (VIntegerNegate fc t) (VIntegerNegate fc' t') = conv env t t'
  conv env (VIntegerClamp fc t) (VIntegerClamp fc' t') = conv env t t'
  conv env (VIntegerToDouble fc t) (VIntegerToDouble fc' t') = conv env t t'
  conv env (VDouble fc) (VDouble fc') = pure ()
  conv env (VDoubleLit fc t) (VDoubleLit fc' t') = convEq fc t t' -- TODO use binary encode
  conv env (VDoubleShow fc t) (VDoubleShow fc' t') = conv env t t'
  conv env (VText fc) (VText fc') = pure ()
  conv env (VTextLit fc t@(MkVChunks xys z)) (VTextLit fc' u@(MkVChunks xys' z')) =
    let l = strFromChunks xys
        r = strFromChunks xys' in
    case (l, r) of
         ((Just l'), (Just r')) => do
           convEq fc (l' ++ z) (r' ++ z')
         _ => convChunks fc env t u
  conv env (VTextAppend fc t u) (VTextAppend fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VTextShow fc t) (VTextShow fc' t') = do
    conv env t t'
  conv env (VTextReplace fc t u v) (VTextReplace fc' t' u' v') = do
    conv env t t'
    conv env u u'
    conv env v v'
  conv env (VList fc a) (VList fc' a') = conv env a a'
  conv env (VListLit fc _ xs) (VListLit fc' _ xs') = convList fc env xs xs'
  conv env (VListAppend fc t u) (VListAppend fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VListBuild fc _ t) (VListBuild fc' _ t') = conv env t t'
  conv env (VListFold fc a l _ t u) (VListFold fc' a' l' _ t' u') = do
    conv env a a'
    conv env l l'
    conv env t t'
    conv env u u'
  conv env (VListLength fc _ t) (VListLength fc' _ t') = conv env t t'
  conv env (VListHead fc _ t) (VListHead fc' _ t') = conv env t t'
  conv env (VListLast fc _ t) (VListLast fc' _ t') = conv env t t'
  conv env (VListIndexed fc _ t) (VListIndexed fc' _ t') = conv env t t'
  conv env (VListReverse fc _ t) (VListReverse fc' _ t') = conv env t t'
  conv env (VOptional fc a) (VOptional fc' a') = conv env a a'
  conv env (VNone fc _) (VNone fc' _) = pure ()
  conv env (VSome fc t) (VSome fc' t') = conv env t t'
  conv env (VEquivalent fc t u) (VEquivalent fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VAssert fc t) (VAssert fc' t') = conv env t t'
  conv env (VRecord fc m) (VRecord fc' m') = do
    case (keys m) == (keys m') of
         True => convList fc env (values m) (values m')
         False => convErr fc m m'
  conv env (VRecordLit fc m) (VRecordLit fc' m') = do
    case (keys m) == (keys m') of
         True => convList fc env (values m) (values m')
         False => convErr fc m m'
  conv env (VUnion fc m) (VUnion fc' m') = do
    convUnion fc env (toList m) (toList m')
  conv env (VCombine fc t u) (VCombine fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VCombineTypes fc t u) (VCombineTypes fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VPrefer fc t u) (VPrefer fc' t' u') = do
    conv env t t'
    conv env u u'
  conv env (VMerge fc t u Nothing) (VMerge fc' t' u' Nothing) = do
    conv env t t'
    conv env u u'
  conv env (VMerge fc t u (Just a)) (VMerge fc' t' u' (Just a')) = do
    conv env t t'
    conv env u u'
    conv env a a'
  conv env (VToMap fc t Nothing) (VToMap fc' t' Nothing) = do
    conv env t t'
  conv env (VToMap fc t (Just a)) (VToMap fc' t' (Just a')) = do
    conv env t t'
    conv env a a'
  conv env (VInject fc m k (Just mt)) (VInject fc' m' k' (Just mt')) = do
    convUnion fc env (toList m) (toList m')
    convEq fc k k'
    conv env mt mt'
  conv env (VInject fc m k Nothing) (VInject fc' m' k' Nothing) = do
    convUnion fc env (toList m) (toList m')
    convEq fc k k'
  conv env (VProject fc t (Left ks)) (VProject fc' t' (Left ks')) = do
    conv env t t'
    convEq fc ks ks'
  conv env (VProject fc t (Right u)) (VProject fc' t' (Right u')) = do
    conv env t t'
    conv env u u'
  conv env (VWith fc t ks u) (VWith fc' t' ks' u') = do
    conv env t t'
    convEq fc ks ks'
    conv env u u'
  conv env (VPrimVar fc) (VPrimVar fc') = pure () -- TODO not in conv, maybe covered by `_ | ptrEq t t' -> True` case?
  conv env t u = convErr (getFC t) t u
