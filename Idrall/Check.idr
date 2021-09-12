module Idrall.Check

import Idrall.Expr
import Idrall.Error
import Idrall.Value
import Idrall.Map
import Idrall.Eval

import Data.List
import Data.List1
import Data.String

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
  qVar x i env = EVar initFC x ((countName' x env) - i - 1)

  quoteBind : Name -> List Name -> Value -> Either Error (Expr Void)
  quoteBind x env = quote (x :: env)

  qApp : List Name -> Expr Void -> Value -> Either Error (Expr Void)
  qApp env t VPrimVar = Right $ t
  qApp env t u        = Right $ EApp t !(quote env u)

  -- Prelude.foldlM : (Foldable t, Monad m) => (a -> b -> m a) -> a -> t b -> m a
  qAppM : List Name -> Expr Void -> List Value -> Either Error (Expr Void)
  qAppM env x args = foldlM (qApp env) x args

  export
  quote : List Name -> Value -> Either Error (Expr Void)
  quote env (VConst fc k) = Right $ EConst k
  quote env (VVar fc x i) = Right $ qVar x i env
  quote env (VApp fc t u) = qApp env !(quote env t) u
  quote env (VLambda fc a b) =
    let (x, v, t) = freshCl b env in
        Right $ ELam x !(quote env a) !(quoteBind x env !(inst t v))
  quote env (VHLam fc (Typed x a) t) =
    let (x', v) = fresh x env in
    Right $ ELam x' !(quote env a) !(quoteBind x env !(t v))
  quote env (VHLam fc NaturalSubtractZero _) =
    pure $ EApp ENaturalSubtract (ENaturalLit 0)
  quote env (VHLam fc _ t) = quote env !(t VPrimVar)
  quote env (VPi fc a b) =
    let (x, v, b') = freshCl b env in
        Right $ EPi x !(quote env a) !(quoteBind x env !(inst b' v))
  quote env (VHPi fc x a b) =
    let (x', v) = fresh x env in
        Right $ EPi x !(quote env a) !(quoteBind x env !(b v))
  quote env (VBool fc) = pure $ EBool initFC
  quote env (VBoolLit fc b) = pure $ EBoolLit initFC b
  quote env (VBoolAnd fc t u) = pure $ EBoolAnd initFC !(quote env t) !(quote env u)
  quote env (VBoolOr fc t u) = pure $ EBoolOr initFC !(quote env t) !(quote env u)
  quote env (VBoolEQ fc t u) = pure $ EBoolEQ initFC !(quote env t) !(quote env u)
  quote env (VBoolNE fc t u) = pure $ EBoolNE initFC !(quote env t) !(quote env u)
  quote env (VBoolIf fc b t f) = pure $ EBoolIf initFC !(quote env b) !(quote env t) !(quote env f)
  quote env (VNatural fc) = Right $ ENatural initFC
  quote env (VNaturalLit fc k) = Right $ ENaturalLit initFC k
  quote env (VNaturalBuild fc x) = qApp env ENaturalBuild initFC x
  quote env (VNaturalFold fc w x y z) = qAppM env ENaturalFold initFC [w, x, y, z]
  quote env (VNaturalIsZero fc x) = qApp env ENaturalIsZero initFC x
  quote env (VNaturalEven fc x) = qApp env ENaturalEven initFC x
  quote env (VNaturalOdd fc x) = qApp env ENaturalOdd initFC x
  quote env (VNaturalToInteger fc x) = qApp env ENaturalToInteger initFC x
  quote env (VNaturalSubtract x y) = qAppM env ENaturalSubtract initFC [x, y]
  quote env (VNaturalShow fc x) = qApp env ENaturalShow initFC x
  quote env (VNaturalPlus fc t u) = Right $ ENaturalPlus initFC !(quote env t) !(quote env u)
  quote env (VNaturalTimes fc t u) = Right $ ENaturalTimes initFC !(quote env t) !(quote env u)
  quote env (VInteger fc) = Right $ EInteger initFC
  quote env (VIntegerLit fc x) = Right $ EIntegerLit initFC x
  quote env (VIntegerShow fc x) = qApp env EIntegerShow initFC x
  quote env (VIntegerNegate fc x) = qApp env EIntegerNegate initFC x
  quote env (VIntegerClamp fc x) = qApp env EIntegerClamp initFC x
  quote env (VIntegerToDouble fc x) = qApp env EIntegerToDouble initFC x
  quote env (VDouble fc) = Right $ EDouble initFC
  quote env (VDoubleLit fc x) = Right $ EDoubleLit initFC x
  quote env (VDoubleShow fc x) = qApp env EDoubleShow initFC x
  quote env (VText fc) = Right $ EText initFC
  quote env (VTextLit fc (MkVChunks xs x)) =
    let chx = traverse (mapChunks (quote env)) xs in
    Right $ ETextLit initFC (MkChunks !chx x)
  quote env (VTextAppend fc t u) = pure $ ETextAppend initFC !(quote env t) !(quote env u)
  quote env (VTextShow fc t) = qApp env ETextShow initFC t
  quote env (VTextReplace fc t u v) = qAppM env ETextReplace initFC [t, u, v]
  quote env (VList fc x) = qApp env EList initFC x
  quote env (VListLit fc Nothing ys) =
    let ys' = traverse (quote env) ys in
    Right $ EListLit initFC Nothing !ys'
  quote env (VListLit fc (Just x) ys) =
    let ys' = traverse (quote env) ys in
    Right $ EListLit initFC (Just !(quote env x)) !ys'
  quote env (VListAppend fc x y) = Right $ EListAppend initFC !(quote env x) !(quote env y)
  quote env (VListBuild fc t u) = qAppM env EListBuild initFC [t, u]
  quote env (VListFold fc a l t u v) = qAppM env EListFold initFC [a, l, t, u, v]
  quote env (VListLength fc t u) = qAppM env EListLength initFC [t, u]
  quote env (VListHead fc t u) = qAppM env EListHead initFC [t, u]
  quote env (VListLast fc t u) = qAppM env EListLast initFC [t, u]
  quote env (VListIndexed fc t u) = qAppM env EListIndexed initFC [t, u]
  quote env (VListReverse fc t u) = qAppM env EListReverse initFC [t, u]
  quote env (VOptional fc x) = qApp env EOptional initFC x
  quote env (VNone fc x) = qApp env ENone initFC x
  quote env (VSome fc x) = Right $ ESome initFC !(quote env x)
  quote env (VEquivalent fc x y) = Right $ EEquivalent initFC !(quote env x) !(quote env y)
  quote env (VAssert fc x) = Right $ EAssert initFC !(quote env x)
  quote env (VRecord fc x) =
    let x' = traverse (quote env) x in
    Right $ ERecord initFC !x'
  quote env (VRecordLit fc x) =
    let x' = traverse (quote env) x in
    Right $ ERecordLit initFC !x'
  quote env (VUnion fc x) =
    let x' = traverse (mapMaybe (quote env)) x in
    Right $ EUnion initFC !x'
  quote env (VField fc x y) = Right $ EField initFC !(quote env x) y
  quote env (VCombine fc x y) = Right $ ECombine initFC !(quote env x) !(quote env y)
  quote env (VCombineTypes fc x y) = Right $ ECombineTypes initFC !(quote env x) !(quote env y)
  quote env (VPrefer fc x y) = Right $ EPrefer !(quote env x) !(quote env y)
  quote env (VMerge fc x y Nothing) = pure $ EMerge !(quote env x) !(quote env y) Nothing
  quote env (VMerge fc x y (Just z)) = pure $ EMerge !(quote env x) !(quote env y) (Just !(quote env z))
  quote env (VToMap fc x Nothing) = pure $ EToMap !(quote env x) Nothing
  quote env (VToMap fc x (Just y)) = pure $ EToMap !(quote env x) (Just !(quote env y))
  quote env (VInject fc m k Nothing) =
    let m' = traverse (mapMaybe (quote env)) m in
    Right $ EField (EUnion !m') k
  quote env (VInject fc m k (Just t)) =
    let m' = traverse (mapMaybe (quote env)) m in
    qApp env (EField (EUnion !m') k) t
  quote env (VProject fc t (Left ks)) = pure $ EProject !(quote env t) (Left ks)
  quote env (VProject fc t (Right u)) = pure $ EProject !(quote env t) (Right $ !(quote env u))
  quote env (VWith fc t ks u) = pure $ EWith !(quote env t) ks !(quote env u)
  quote env (VPrimVar fc) = Left $ ReadBackError "Can't quote VPrimVar"

||| destruct VPi and VHPi
vAnyPi : Value -> Either Error (Name, Ty, (Value -> Either Error Value))
vAnyPi (VHPi x a b) = Right (x, a, b)
vAnyPi (VPi a b@(MkClosure x _ _)) = Right (x, a, inst b)
vAnyPi t = Left $ Unexpected $ show t ++ " is not a VPi or VHPi"

data Types = TEmpty
           | TBind Types Name Value

Show Types where
  show TEmpty = "TEmpty"
  show (TBind x y z) = "(TBind " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"

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

Show Cxt where
  show x = "(MkCxt { values = " ++ show (values x) ++ ", types = " ++ show 2 ++ "})"

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
      other        => Left $ ErrorMessage $ show other ++ " is not a Type/Kind/Sort"

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
    go TEmpty n = Left $ MissingVar $ x ++ "@" ++ show i ++ "\n in Cxt: " ++ show cxt
    go (TBind ts x' a) n =
      case x == x' of
           True => if n == 0 then Right (EVar x i, a) else go ts (n - 1)
           False => go ts n
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
    _ <- check cxt u a
    Right $ (EApp t u, !(b !(eval (values cxt) u)))
  infer cxt (ELet x Nothing a b) = do
    (a, aa) <- infer cxt a
    v <- eval (values cxt) a
    infer (define x v aa cxt) b
  infer cxt (ELet x (Just t) a b) = do
    tt <- eval (values cxt) t
    _ <- check cxt a tt
    v <- eval (values cxt) a
    infer (define x v tt cxt) b
  infer cxt (EAnnot x t) = do
    tv <- eval (values cxt) t
    _ <- check cxt x tv
    Right $ (EAnnot x t, tv)
  infer cxt EBool = Right $ (EBool, VConst CType)
  infer cxt (EBoolLit x) = Right $ (EBoolLit x, VBool)
  infer cxt (EBoolAnd x y) = do
    _ <- check cxt x VBool
    _ <- check cxt y VBool
    Right $ (EBoolAnd x y, VBool)
  infer cxt (EBoolOr x y) = do
    _ <- check cxt x VBool
    _ <- check cxt y VBool
    Right $ (EBoolOr x y, VBool)
  infer cxt (EBoolEQ x y) = do
    _ <- check cxt x VBool
    _ <- check cxt y VBool
    Right $ (EBoolEQ x y, VBool)
  infer cxt (EBoolNE x y) = do
    _ <- check cxt x VBool
    _ <- check cxt y VBool
    Right $ (EBoolNE x y, VBool)
  infer cxt (EBoolIf b t f) = do
    _ <- check cxt b VBool
    (t, tt) <- infer cxt t
    _ <- check cxt f tt
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
    _ <- check cxt t VNatural
    _ <- check cxt u VNatural
    Right $ (ENaturalPlus t u, VNatural)
  infer cxt (ENaturalTimes t u) = do
    _ <- check cxt t VNatural
    _ <- check cxt u VNatural
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
    _ <- traverse go xs
    Right $ (ETextLit (MkChunks xs x), VText)
  infer cxt (ETextAppend t u) = do
    _ <- check cxt t VText
    _ <- check cxt u VText
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
    _ <- traverse (\e => check cxt e ty) xs
    Right $ (EListLit Nothing (x :: xs), VList ty)
  infer cxt (EListLit (Just a) []) = do
    case !(eval (values cxt) a) of
         VList a' => do
           ea' <- quote (envNames $ values cxt) a'
           _ <- check cxt ea' (VConst CType)
           Right $ (EListLit (Just a) [], VList a')
         other => Left $ ErrorMessage $ "Not a list annotation: " ++ show other
  infer cxt (EListLit (Just a) (x :: xs)) = do
    ty <- eval (values cxt) a
    (a', av) <- infer cxt x
    _ <- traverse (\e => check cxt e av) xs
    _ <- conv (values cxt) ty (VList av)
    Right $ (EListLit (Just a) (x :: xs), ty)
  infer cxt (EListAppend t u) = do
    (t', tt) <- infer cxt t
    case tt of
         (VList x) => do
           _ <- check cxt u tt
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
    _ <- check cxt !(quote (envNames $ values cxt) tt) vType -- TODO abstract this out?
    pure (ESome t, VOptional tt)
  infer cxt ENone =
    Right $ (ENone, VHPi "a" vType $ \a => Right $ (VOptional a))
  infer cxt e@(EEquivalent t u) = do
    (t, tt) <- infer cxt t
    _ <- check cxt u tt
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
  infer cxt (EToMap t a) = do
    (t, tt) <- infer cxt t
    case tt of
         (VRecord ms) =>
           let xs = SortedMap.toList ms in
           case (xs, a) of
                (((k, v) :: ys), Just x) => do
                  _ <- unifyAllValues cxt v ys
                  _ <- unify cxt (toMapTy v) !(eval (values cxt) x)
                  pure (EToMap t a, toMapTy v)
                (((k, v) :: ys), Nothing) => do
                  _ <- unifyAllValues cxt v ys
                  pure (EToMap t a, toMapTy v)
                ([], Just x) => do v <- checkToMapAnnot cxt !(eval (values cxt) x)
                                   pure (EToMap t a, v)
                ([], Nothing) => Left $ ToMapEmpty "Needs an annotation"
         other => unexpected "Not a RecordLit" other
  where
    unifyAllValues : Cxt -> Value -> List (FieldName, Value) -> Either Error Value
    unifyAllValues cxt v vs = do
      unify cxt !(inferSkip cxt !(quote (envNames $ values cxt) v)) (VConst CType)
      _ <- foldlM (\x,y => unify cxt x y *> pure x) v (map snd vs)
      pure v
    checkToMapAnnot : Cxt -> Value -> Either Error Value
    checkToMapAnnot cxt v@(VList (VRecord ms)) =
      case SortedMap.toList ms of
           (((MkFieldName "mapKey"), VText) :: ((MkFieldName "mapValue"), a) :: []) => do
             _ <- checkTy cxt !(quote (envNames $ values cxt) a)
             pure v
           other => Left $ ToMapError $ "wrong annotation type" ++ show other
    checkToMapAnnot cxt other = Left $ ToMapError $ "wrong annotation type: " ++ show other
  infer cxt (EField t k) = do
    (t, tt) <- infer cxt t
    case tt of
         (VConst _) =>
            case !(eval (values cxt) t) of
                 VUnion ts =>
                    case lookup k ts of
                         (Just Nothing) => pure $ (EField t k, VUnion ts)
                         (Just (Just a)) => pure $ (EField t k, vFun a (VUnion ts))
                         Nothing => Left $ FieldNotFoundError $ show k
                 x => Left (InvalidFieldType (show t))
         (VRecord ts) =>
            case lookup k ts of
                 (Just a) => pure $ (EField t k, a)
                 Nothing => Left $ FieldNotFoundError $ show k
         _ => Left (InvalidFieldType (show t))
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
  infer cxt (EImportAlt x y) = infer cxt x
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
    case toList1' xs of
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
