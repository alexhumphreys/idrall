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
fresh x env = (x, VVar initFC x (countName' x env))

freshCl : Closure -> List Name -> (Name, Value, Closure)
freshCl cl@(MkClosure x _ _) env = (x, snd (fresh x env), cl)

mutual
  qVar : FC -> Name -> Int -> List Name -> Expr Void
  qVar fc x i env = EVar fc x ((countName' x env) - i - 1)

  quoteBind : Name -> List Name -> Value -> Either Error (Expr Void)
  quoteBind x env = quote (x :: env)

  qApp : FC -> List Name -> Expr Void -> Value -> Either Error (Expr Void)
  qApp _ env t (VPrimVar fc) = pure $ t
  qApp fc env t u        = pure $ EApp fc t !(quote env u)

  -- Prelude.foldlM : (Foldable t, Monad m) => (a -> b -> m a) -> a -> t b -> m a
  qAppM : FC -> List Name -> Expr Void -> List Value -> Either Error (Expr Void)
  qAppM fc env x args = foldlM (qApp fc env) x args

  export
  quote : List Name -> Value -> Either Error (Expr Void)
  quote env (VConst fc k) = pure $ EConst fc k
  quote env (VVar fc x i) = pure $ qVar fc x i env
  quote env (VApp fc t u) = qApp fc env !(quote env t) u
  quote env (VLambda fc a b) =
    let (x, v, t) = freshCl b env in
        pure $ ELam fc x !(quote env a) !(quoteBind x env !(inst t v))
  quote env (VHLam fc (Typed x a) t) =
    let (x', v) = fresh x env in
    pure $ ELam fc x' !(quote env a) !(quoteBind x env !(t v))
  quote env (VHLam fc NaturalSubtractZero _) =
    pure $ EApp fc (ENaturalSubtract initFC) (ENaturalLit initFC 0)
  quote env (VHLam fc _ t) = quote env !(t $ VPrimVar initFC)
  quote env (VPi fc a b) =
    let (x, v, b') = freshCl b env in
        pure $ EPi fc x !(quote env a) !(quoteBind x env !(inst b' v))
  quote env (VHPi fc x a b) =
    let (x', v) = fresh x env in
        pure $ EPi fc x !(quote env a) !(quoteBind x env !(b v))
  quote env (VBool fc) = pure $ EBool fc
  quote env (VBoolLit fc b) = pure $ EBoolLit fc b
  quote env (VBoolAnd fc t u) = pure $ EBoolAnd fc !(quote env t) !(quote env u)
  quote env (VBoolOr fc t u) = pure $ EBoolOr fc !(quote env t) !(quote env u)
  quote env (VBoolEQ fc t u) = pure $ EBoolEQ fc !(quote env t) !(quote env u)
  quote env (VBoolNE fc t u) = pure $ EBoolNE fc !(quote env t) !(quote env u)
  quote env (VBoolIf fc b t f) = pure $ EBoolIf fc !(quote env b) !(quote env t) !(quote env f)
  quote env (VNatural fc) = pure $ ENatural fc
  quote env (VNaturalLit fc k) = pure $ ENaturalLit fc k
  quote env (VNaturalBuild fc x) = qApp fc env (ENaturalBuild fc) x
  quote env (VNaturalFold fc w x y z) = qAppM fc env (ENaturalFold fc) [w, x, y, z]
  quote env (VNaturalIsZero fc x) = qApp fc env (ENaturalIsZero fc) x
  quote env (VNaturalEven fc x) = qApp fc env (ENaturalEven fc) x
  quote env (VNaturalOdd fc x) = qApp fc env (ENaturalOdd fc) x
  quote env (VNaturalToInteger fc x) = qApp fc env (ENaturalToInteger fc) x
  quote env (VNaturalSubtract fc x y) = qAppM fc env (ENaturalSubtract fc) [x, y]
  quote env (VNaturalShow fc x) = qApp fc env (ENaturalShow fc) x
  quote env (VNaturalPlus fc t u) = pure $ ENaturalPlus fc !(quote env t) !(quote env u)
  quote env (VNaturalTimes fc t u) = pure $ ENaturalTimes fc !(quote env t) !(quote env u)
  quote env (VInteger fc) = pure $ EInteger fc
  quote env (VIntegerLit fc x) = pure $ EIntegerLit fc x
  quote env (VIntegerShow fc x) = qApp fc env (EIntegerShow fc) x
  quote env (VIntegerNegate fc x) = qApp fc env (EIntegerNegate fc) x
  quote env (VIntegerClamp fc x) = qApp fc env (EIntegerClamp fc) x
  quote env (VIntegerToDouble fc x) = qApp fc env (EIntegerToDouble fc) x
  quote env (VDouble fc) = pure $ EDouble fc
  quote env (VDoubleLit fc x) = pure $ EDoubleLit fc x
  quote env (VDoubleShow fc x) = qApp fc env (EDoubleShow fc) x
  quote env (VText fc) = pure $ EText fc
  quote env (VTextLit fc (MkVChunks xs x)) =
    let chx = traverse (mapChunks (quote env)) xs in
    pure $ ETextLit initFC (MkChunks !chx x)
  quote env (VTextAppend fc t u) = pure $ ETextAppend fc !(quote env t) !(quote env u)
  quote env (VTextShow fc t) = qApp fc env (ETextShow fc) t
  quote env (VTextReplace fc t u v) = qAppM fc env (ETextReplace fc) [t, u, v]
  quote env (VList fc x) = qApp fc env (EList fc) x
  quote env (VListLit fc Nothing ys) =
    let ys' = traverse (quote env) ys in
    pure $ EListLit fc Nothing !ys'
  quote env (VListLit fc (Just x) ys) =
    let ys' = traverse (quote env) ys in
    pure $ EListLit fc (Just !(quote env x)) !ys'
  quote env (VListAppend fc x y) = pure $ EListAppend fc !(quote env x) !(quote env y)
  quote env (VListBuild fc t u) = qAppM fc env (EListBuild fc) [t, u]
  quote env (VListFold fc a l t u v) = qAppM fc env (EListFold fc) [a, l, t, u, v]
  quote env (VListLength fc t u) = qAppM fc env (EListLength fc) [t, u]
  quote env (VListHead fc t u) = qAppM fc env (EListHead fc) [t, u]
  quote env (VListLast fc t u) = qAppM fc env (EListLast fc) [t, u]
  quote env (VListIndexed fc t u) = qAppM fc env (EListIndexed fc) [t, u]
  quote env (VListReverse fc t u) = qAppM fc env (EListReverse fc) [t, u]
  quote env (VOptional fc x) = qApp fc env (EOptional fc) x
  quote env (VNone fc x) = qApp fc env (ENone fc) x
  quote env (VSome fc x) = pure $ ESome fc !(quote env x)
  quote env (VEquivalent fc x y) = pure $ EEquivalent fc !(quote env x) !(quote env y)
  quote env (VAssert fc x) = pure $ EAssert fc !(quote env x)
  quote env (VRecord fc x) =
    let x' = traverse (quote env) x in
    pure $ ERecord fc !x'
  quote env (VRecordLit fc x) =
    let x' = traverse (quote env) x in
    pure $ ERecordLit fc !x'
  quote env (VUnion fc x) =
    let x' = traverse (mapMaybe (quote env)) x in
    pure $ EUnion fc !x'
  quote env (VCombine fc x y) = pure $ ECombine fc !(quote env x) !(quote env y)
  quote env (VCombineTypes fc x y) = pure $ ECombineTypes fc !(quote env x) !(quote env y)
  quote env (VPrefer fc x y) = pure $ EPrefer fc !(quote env x) !(quote env y)
  quote env (VMerge fc x y Nothing) = pure $ EMerge fc !(quote env x) !(quote env y) Nothing
  quote env (VMerge fc x y (Just z)) = pure $ EMerge fc !(quote env x) !(quote env y) (Just !(quote env z))
  quote env (VToMap fc x Nothing) = pure $ EToMap fc !(quote env x) Nothing
  quote env (VToMap fc x (Just y)) = pure $ EToMap fc !(quote env x) (Just !(quote env y))
  quote env (VField fc x y) = pure $ EField fc !(quote env x) y
  quote env (VInject fc m k Nothing) =
    let m' = traverse (mapMaybe (quote env)) m in
    pure $ EField fc (EUnion initFC !m') k
  quote env (VInject fc m k (Just t)) =
    let m' = traverse (mapMaybe (quote env)) m in
    qApp fc env (EField fc (EUnion initFC !m') k) t
  quote env (VProject fc t (Left ks)) = pure $ EProject fc !(quote env t) (Left ks)
  quote env (VProject fc t (Right u)) = pure $ EProject fc !(quote env t) (pure $ !(quote env u))
  quote env (VWith fc t ks u) = pure $ EWith fc !(quote env t) ks !(quote env u)
  quote env (VPrimVar fc) = Left $ ReadBackError "Can't quote VPrimVar"

||| destruct VPi and VHPi
vAnyPi : Value -> Either Error (Name, Ty, (Value -> Either Error Value))
vAnyPi (VHPi fc x a b) = pure (x, a, b)
vAnyPi (VPi fc a b@(MkClosure x _ _)) = pure (x, a, inst b)
vAnyPi t = Left $ Unexpected $ show t ++ " is not a VPi or VHPi"

data Types = TEmpty
           | TBind Types Name Value

Show Types where
  show TEmpty = "TEmpty"
  show (TBind x y z) = "(TBind " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"

axiom : U -> Either Error U
axiom CType = pure Kind
axiom Kind = pure Sort
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
      VConst fc c => pure (t, c)
      other        => Left $ ErrorMessage $ show other ++ " is not a Type/Kind/Sort"

  ||| returns the original `Expr Void` on success
  export
  check : Cxt -> Expr Void -> Value -> Either Error (Expr Void)
  check cxt (EConst fc CType) vKype = pure $ EConst fc CType
  check cxt (EConst fc Kind) vSort = pure $ EConst fc Kind
  check cxt (EConst fc Sort) z = Left $ SortError
  check cxt (ELam fc x a t) pi =
    let (x', v) = fresh x (envNames (values cxt)) in do -- TODO not sure about fresh...
    (_, a', b) <- vAnyPi pi
    (a, _) <- checkTy cxt a
    av <- eval (values cxt) a
    unify cxt av a'
    t <- check (define x' v av cxt) t !(b v)
    pure $ ELam fc x a t
  check cxt (EBoolLit fc t) (VBool fc') = pure $ EBoolLit fc t
  check cxt (ENaturalLit fc t) (VNatural fc') = pure $ ENaturalLit fc t
  check cxt (EIntegerLit fc t) (VInteger fc') = pure $ EIntegerLit fc t
  check cxt (EDoubleLit fc t) (VDouble fc') = pure $ EDoubleLit fc t
  check cxt (ETextLit fc t) (VText fc') = pure $ ETextLit fc t
  -- check cxt (ERecordLit y) z = ?check_rhs TODO maybe add this later for performance?
  check cxt t a = do
    (t, a') <- infer cxt t
    unify cxt a' a
    pure t

  unexpected : String -> Value -> Either Error a
  unexpected str v = Left (Unexpected $ str ++ " Value: " ++ show v)

  natFoldTy : FC -> Value
  natFoldTy fc =
    VHPi fc "natural" vType $ \natural =>
    pure $ VHPi fc "succ" (vFun natural natural) $ \succ =>
    pure $ VHPi fc "zero" natural $ \zero =>
    pure $ natural

  listFoldTy : FC -> Value -> Value
  listFoldTy fc a =
    VHPi fc "list" vType $ \list =>
    pure $ VHPi fc "cons" (vFun a $ vFun list list) $ \cons =>
    pure $ VHPi fc "nil" list $ \nil =>
    pure $ list

  ||| returns a pair (Expr, Value), which is original Expr, and it's type as a Value
  export
  infer : Cxt -> Expr Void -> Either Error (Expr Void, Value)
  infer cxt (EConst fc k) = (\k' => (EConst fc k, VConst fc k')) <$> axiom k
  infer cxt (EVar fc x i) = go (types cxt) i
  where
    go : Types -> Int -> Either Error (Expr Void, Value)
    go TEmpty n = Left $ MissingVar $ x ++ "@" ++ show i ++ "\n in Cxt: " ++ show cxt
    go (TBind ts x' a) n =
      case x == x' of
           True => if n == 0 then pure (EVar fc x i, a) else go ts (n - 1)
           False => go ts n
  infer cxt (ELam fc x a t) = do
    (a, ak) <- checkTy cxt a
    av <- eval (values cxt) a
    (t, b) <- infer (bind x av cxt) t
    nb <- quote (x :: (envNames (values cxt))) b
    pure ( ELam fc x a t
          , VHPi fc x av $
            \u => pure $ !(eval (Extend (values cxt) x u) nb)) -- TODO check i'm using values right
  infer cxt (EPi fc x a b) = do
    (a, ak) <- checkTy cxt a
    av <- eval (values cxt) a
    (b, bk) <- checkTy (bind x av cxt) b
    pure (EPi fc x a b, VConst fc $ rule ak bk)
  infer cxt (EApp fc t u) = do
    (t, tt) <- infer cxt t
    (x, a, b) <- vAnyPi tt
    _ <- check cxt u a
    pure $ (EApp fc t u, !(b !(eval (values cxt) u)))
  infer cxt (ELet fc x Nothing a b) = do
    (a, aa) <- infer cxt a
    v <- eval (values cxt) a
    infer (define x v aa cxt) b
  infer cxt (ELet fc x (Just t) a b) = do
    tt <- eval (values cxt) t
    _ <- check cxt a tt
    v <- eval (values cxt) a
    infer (define x v tt cxt) b
  infer cxt (EAnnot fc x t) = do
    tv <- eval (values cxt) t
    _ <- check cxt x tv
    pure $ (EAnnot fc x t, tv)
  infer cxt (EBool fc) = pure $ (EBool fc, VConst fc CType)
  infer cxt (EBoolLit fc x) = pure $ (EBoolLit fc x, VBool fc)
  infer cxt (EBoolAnd fc x y) = do
    _ <- check cxt x (VBool fc)
    _ <- check cxt y (VBool fc)
    pure $ (EBoolAnd fc x y, VBool fc)
  infer cxt (EBoolOr fc x y) = do
    _ <- check cxt x (VBool initFC)
    _ <- check cxt y (VBool initFC)
    pure $ (EBoolOr fc x y, VBool fc)
  infer cxt (EBoolEQ fc x y) = do
    _ <- check cxt x (VBool initFC)
    _ <- check cxt y (VBool initFC)
    pure $ (EBoolEQ fc x y, VBool fc)
  infer cxt (EBoolNE fc x y) = do
    _ <- check cxt x (VBool initFC)
    _ <- check cxt y (VBool initFC)
    pure $ (EBoolNE fc x y, VBool fc)
  infer cxt (EBoolIf fc b t f) = do
    _ <- check cxt b (VBool initFC)
    (t, tt) <- infer cxt t
    _ <- check cxt f tt
    pure $ (EBoolIf fc b t f, tt)
  infer cxt (ENatural fc) = pure $ (ENatural fc, VConst fc CType)
  infer cxt (ENaturalLit fc k) = pure $ (ENaturalLit fc k, VNatural initFC)
  infer cxt (ENaturalBuild fc) = pure $ (ENaturalBuild fc, vFun (natFoldTy initFC) (VNatural initFC))
  infer cxt (ENaturalFold fc) = pure (ENaturalFold fc, vFun (VNatural initFC) (natFoldTy initFC))
  infer cxt (ENaturalIsZero fc) = pure $ (ENaturalIsZero fc, (vFun (VNatural initFC) (VBool initFC)))
  infer cxt (ENaturalEven fc) = pure $ (ENaturalEven fc, (vFun (VNatural initFC) (VBool initFC)))
  infer cxt (ENaturalOdd fc) = pure $ (ENaturalOdd fc, (vFun (VNatural initFC) (VBool initFC)))
  infer cxt (ENaturalSubtract fc) = pure $ (ENaturalOdd fc, (vFun (VNatural initFC) (vFun (VNatural initFC) (VNatural initFC))))
  infer cxt (ENaturalToInteger fc) = pure $ (ENaturalToInteger fc, (vFun (VNatural initFC) (VInteger initFC)))
  infer cxt (ENaturalShow fc) = pure $ (ENaturalShow fc, (vFun (VNatural initFC) (VText initFC)))
  infer cxt (ENaturalPlus fc t u) = do
    _ <- check cxt t (VNatural initFC)
    _ <- check cxt u (VNatural initFC)
    pure $ (ENaturalPlus fc t u, VNatural fc)
  infer cxt (ENaturalTimes fc t u) = do
    _ <- check cxt t (VNatural initFC)
    _ <- check cxt u (VNatural initFC)
    pure $ (ENaturalTimes fc t u, VNatural fc)
  infer cxt (EInteger fc) = pure $ (EInteger fc, VConst fc CType)
  infer cxt (EIntegerLit fc x) = pure $ (EIntegerLit fc x, VInteger initFC)
  infer cxt (EIntegerShow fc) = pure $ (EIntegerShow fc, (vFun (VInteger initFC) (VText initFC)))
  infer cxt (EIntegerNegate fc) = pure $ (EIntegerNegate fc, (vFun (VInteger initFC) (VInteger initFC)))
  infer cxt (EIntegerClamp fc) = pure $ (EIntegerNegate fc, (vFun (VInteger initFC) (VNatural initFC)))
  infer cxt (EIntegerToDouble fc) = pure $ (EIntegerNegate fc, (vFun (VInteger initFC) (VDouble initFC)))
  infer cxt (EDouble fc) = pure $ (EDouble fc, VConst fc CType)
  infer cxt (EDoubleLit fc x) = pure $ (EDoubleLit fc x, VDouble initFC)
  infer cxt (EDoubleShow fc) = pure $ (EDoubleShow fc, (vFun (VDouble initFC) (VText initFC)))
  infer cxt (EText fc) = pure $ (EText fc, VConst initFC CType)
  infer cxt (ETextLit fc (MkChunks xs x)) =
    let go = mapChunks (\e => check cxt e (VText initFC)) in do
    _ <- traverse go xs
    pure $ (ETextLit fc (MkChunks xs x), (VText initFC))
  infer cxt (ETextAppend fc t u) = do
    _ <- check cxt t (VText initFC)
    _ <- check cxt u (VText initFC)
    pure $ (ETextAppend fc t u, VText initFC)
  infer cxt (ETextShow fc) = pure $ (EIntegerShow fc, (vFun (VText initFC) (VText initFC)))
  infer cxt (ETextReplace fc) =
    pure ( ETextReplace fc,
           VHPi fc "needle" (VText initFC) $ \needle =>
           pure $ VHPi fc "replacement" (VText initFC) $ \replacement =>
           pure $ VHPi fc "haystack" (VText initFC) $ \haystack =>
           pure $ VText initFC)
  infer cxt (EList fc) = do
    pure $ (EList fc, VHPi fc "a" vType $ \a => pure $ vType)
  infer cxt (EListLit fc Nothing []) = do
    Left $ ErrorMessage "Not type for list" -- TODO better error message
  infer cxt (EListLit fc Nothing (x :: xs)) = do
    (x', ty) <- infer cxt x
    _ <- traverse (\e => check cxt e ty) xs
    pure $ (EListLit fc Nothing (x :: xs), VList fc ty)
  infer cxt (EListLit fc (Just a) []) = do
    case !(eval (values cxt) a) of
         VList _ a' => do
           ea' <- quote (envNames $ values cxt) a'
           _ <- check cxt ea' (VConst initFC CType)
           pure $ (EListLit fc (Just a) [], VList fc a')
         other => Left $ ErrorMessage $ "Not a list annotation: " ++ show other
  infer cxt (EListLit fc (Just a) (x :: xs)) = do
    ty <- eval (values cxt) a
    (a', av) <- infer cxt x
    _ <- traverse (\e => check cxt e av) xs
    _ <- conv (values cxt) ty (VList initFC av)
    pure $ (EListLit fc (Just a) (x :: xs), ty)
  infer cxt (EListAppend fc t u) = do
    (t', tt) <- infer cxt t
    case tt of
         (VList _ x) => do
           _ <- check cxt u tt
           pure $ (EListAppend fc t u, tt)
         _ => Left $ ListAppendError "not a list" -- TODO better error message
  infer cxt (EListBuild fc) =
    pure (EListBuild fc, VHPi fc "a" vType $ \a => pure $ vFun (listFoldTy fc a) (VList fc a))
  infer cxt (EListFold fc) =
    pure (EListFold fc, VHPi fc "a" vType $ \a => pure $ vFun (VList fc a) (listFoldTy fc a))
  infer cxt (EListLength fc) =
    pure (EListLength fc, VHPi fc "a" vType $ \a => pure $ vFun (VList fc a) (VNatural fc))
  infer cxt (EListHead fc) =
    pure (EListHead fc, VHPi fc "a" vType $ \a => pure $ vFun (VList fc a) (VOptional fc a))
  infer cxt (EListLast fc) =
    pure (EListLast fc, VHPi fc "a" vType $ \a => pure $ vFun (VList fc a) (VOptional fc a))
  infer cxt (EListIndexed fc) =
    pure (EListIndexed fc
         , VHPi fc "a" vType $ \a =>
           pure $ vFun (VList fc a)
                  (VList fc (VRecord initFC (fromList [(MkFieldName "index", VNatural initFC), (MkFieldName "value", a)]))))
  infer cxt (EListReverse fc) =
    pure (EListReverse fc, VHPi fc "a" vType $ \a => pure $ vFun (VList initFC a) (VList initFC a))
  infer cxt (EOptional fc) =
    pure $ (EOptional fc, VHPi fc "a" vType $ \a => pure $ vType)
  infer cxt (ESome fc t) = do
    (t, tt) <- infer cxt t
    _ <- check cxt !(quote (envNames $ values cxt) tt) vType -- TODO abstract this out?
    pure (ESome fc t, VOptional fc tt)
  infer cxt (ENone fc) =
    pure $ (ENone fc, VHPi fc "a" vType $ \a => pure $ (VOptional fc a))
  infer cxt e@(EEquivalent fc t u) = do
    (t, tt) <- infer cxt t
    _ <- check cxt u tt
    -- conv (values cxt) tt vType TODO
    pure (e, vType)
  infer cxt (EAssert fc (EEquivalent fc' a b)) = do
    (a, aa) <- infer cxt a
    av <- eval (values cxt) a
    bv <- eval (values cxt) b
    conv (values cxt) av bv
    pure (EAssert fc (EEquivalent fc' a b), VEquivalent fc' av bv)
  infer cxt (EAssert fc _) = Left $ AssertError "not an EEquivalent type" -- TODO better error message
  infer cxt (ERecord fc x) = do
    xs' <- traverse (inferSkip cxt) x
    pure $ (ERecord fc x, VConst fc (getHighestType xs'))
  infer cxt (ERecordLit fc x) = do
    xs' <- traverse (inferSkip cxt) x
    pure $ (ERecordLit fc x, VRecord fc xs')
  infer cxt (EUnion fc x) = do
    xs' <- traverse (mapMaybe (inferSkip cxt)) x
    pure $ (EUnion fc x, VConst fc (getHighestTypeM xs'))
  infer cxt (ECombine fc t u) = do
    (t, tt) <- infer cxt t
    (u, uu) <- infer cxt u
    case (tt, uu) of
         (VRecord _ a', VRecord _ b') => do
           ty <- mergeWithApp (doCombine fc) a' b'
           pure $ (ECombine fc t u, VRecord fc ty)
         (VRecord _ _, other) => unexpected "Not a RecordLit" other
         (other, _) => unexpected "Not a RecordLit" other
  infer cxt (ECombineTypes fc a b) = do -- TODO lot of traversals here
    av <- eval (values cxt) a
    bv <- eval (values cxt) b
    case (av, bv) of
         (VRecord _ a', VRecord _ b') => do
           ty <- mergeWithApp (doCombine fc) a' b'
           pure $ (ECombineTypes fc a b, snd !(infer cxt !(quote (envNames $ values cxt) (VRecord fc ty))))
         (other, _) => unexpected "Not a Record" other
  infer cxt (EPrefer fc t u) = do
    (t, tt) <- infer cxt t
    (u, uu) <- infer cxt u
    case (tt, uu) of
         (VRecord _ a', VRecord _ b') => do
           ty <- mergeWithApp' (doCombine fc) a' b'
           pure $ (EPrefer fc t u, VRecord fc ty)
         (VRecord _ _, other) => unexpected "Not a RecordLit" other
         (other, _) => unexpected "Not a RecordLit" other
  infer cxt (EMerge fc t u a) = do
    (u, ut) <- infer cxt u
    (t, tt) <- infer cxt t
    case (ut, tt) of
         (VUnion _ ts, VRecord _ us) => do
           case a of
                Nothing => do
                  pure (EMerge fc t u a, !(inferMerge cxt ts us Nothing))
                (Just a') => do
                  av <- eval (values cxt) a'
                  ty <- inferMerge cxt ts us (Just av)
                  conv (values cxt) av ty
                  pure (EMerge fc t u a, av)
         (VOptional _ a', VRecord _ us) =>
           let newUnion = SortedMap.fromList $
                            [(MkFieldName "None", Nothing), (MkFieldName "Some", Just a')]
           in pure (EMerge fc t u a, !(inferMerge cxt newUnion us Nothing))
         (other, VRecord _ _) => unexpected "Not a RecordLit or Optional" other
         (_, other) => unexpected "Not a RecordLit" other
  infer cxt (EToMap fc t a) = do
    (t, tt) <- infer cxt t
    case tt of
         (VRecord _ ms) =>
           let xs = SortedMap.toList ms in
           case (xs, a) of
                (((k, v) :: ys), Just x) => do
                  _ <- unifyAllValues cxt v ys
                  _ <- unify cxt (toMapTy v) !(eval (values cxt) x)
                  pure (EToMap fc t a, toMapTy v)
                (((k, v) :: ys), Nothing) => do
                  _ <- unifyAllValues cxt v ys
                  pure (EToMap fc t a, toMapTy v)
                ([], Just x) => do v <- checkToMapAnnot cxt !(eval (values cxt) x)
                                   pure (EToMap fc t a, v)
                ([], Nothing) => Left $ ToMapEmpty "Needs an annotation"
         other => unexpected "Not a RecordLit" other
  where
    unifyAllValues : Cxt -> Value -> List (FieldName, Value) -> Either Error Value
    unifyAllValues cxt v vs = do
      unify cxt !(inferSkip cxt !(quote (envNames $ values cxt) v)) (VConst initFC CType)
      _ <- foldlM (\x,y => unify cxt x y *> pure x) v (map snd vs)
      pure v
    checkToMapAnnot : Cxt -> Value -> Either Error Value
    checkToMapAnnot cxt v@(VList fc (VRecord fc' ms)) =
      case SortedMap.toList ms of
           (((MkFieldName "mapKey"), VText initFC) :: ((MkFieldName "mapValue"), a) :: []) => do
             _ <- checkTy cxt !(quote (envNames $ values cxt) a)
             pure v
           other => Left $ ToMapError $ "wrong annotation type" ++ show other
    checkToMapAnnot cxt other = Left $ ToMapError $ "wrong annotation type: " ++ show other
  infer cxt (EField fc t k) = do
    (t, tt) <- infer cxt t
    case tt of
         (VConst _ _) =>
            case !(eval (values cxt) t) of
                 VUnion _ ts =>
                    case lookup k ts of
                         (Just Nothing) => pure $ (EField fc t k, VUnion fc ts)
                         (Just (Just a)) => pure $ (EField fc t k, vFun a (VUnion fc ts))
                         Nothing => Left $ FieldNotFoundError $ show k
                 x => Left (InvalidFieldType (show t))
         (VRecord _ ts) =>
            case lookup k ts of
                 (Just a) => pure $ (EField fc t k, a)
                 Nothing => Left $ FieldNotFoundError $ show k
         _ => Left (InvalidFieldType (show t))
  infer cxt (ERecordCompletion fc t u) = do
    (t, tt) <- infer cxt t
    case tt of
         (VRecord _ ms) => do
           -- guard $ mapErr "Type" (go (MkFieldName "Type") ms)
           -- guard $ mapErr "default" (go (MkFieldName "default") ms)
           case (lookup (MkFieldName "Type") ms, lookup (MkFieldName "default") ms) of
                (Just x, Just y) =>
                  infer cxt (EAnnot fc (EPrefer fc (EField fc t (MkFieldName "default")) u) (EField fc t (MkFieldName "Type")))
                (other, (Just _)) => Left $ InvalidRecordCompletion "Type"
                (_, other) => Left $ InvalidRecordCompletion "default"
         other => unexpected "Not a RecordLit" other
  infer cxt (EProject fc t (Left ks)) = do
    (t, tt) <- infer cxt t
    case tt of
         (VRecord _ ms) =>
           pure (EProject fc t (Left ks), VRecord fc $ fromList !(vProjectByFields ms ks))
         (other) => unexpected "Not a RecordLit" other
  infer cxt (EProject fc t (Right a)) = do
    (t, tt) <- infer cxt t
    av <- eval (values cxt) a
    case (tt, av) of
         (VRecord _ ms, VRecord _ ms') => do
           pure (EProject fc t (Right a), VRecord fc $ fromList !(vProjectByFields ms (keys ms')))
         (other, VRecord _ _) => unexpected "Not a RecordLit" other
         (_, other) => unexpected "Not a Record" other
  infer cxt (EWith fc t ks u) = do -- TODO understand this
    (t, tt) <- infer cxt t
    pure (EWith fc t ks u, !(inferWith tt ks u))
  where
    inferWith : Value -> List1 FieldName -> Expr Void -> Either Error Value
    inferWith (VRecord fc ms) ks y =
      case ks of
           (head ::: []) => do
             (u, uu) <- infer cxt u
             pure $ VRecord fc $ insert head uu ms
           (head ::: (k :: ks)) => do
             let v = case lookup head ms of
                      Nothing => VRecord fc (fromList [])
                      (Just v) => v
             v' <- inferWith v (k ::: ks) y
             pure $ VRecord fc $ insert head v' ms
    inferWith other _ _ = unexpected "Not a RecordLit" other
  infer cxt (EImportAlt fc x y) = infer cxt x
  infer cxt (EEmbed fc (Raw x)) = absurd x
  infer cxt (EEmbed fc (Resolved x)) = infer initCxt x

  toMapTy : Value -> Value
  toMapTy v = VList initFC $ VRecord initFC $ fromList [(MkFieldName "mapKey", VText initFC), (MkFieldName "mapValue", v)]

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
  inferSkip cxt = (\e => pure $ snd !(infer cxt e))

  pickHigherType : (acc : U) -> Ty -> U
  pickHigherType CType (VConst _ Kind) = Kind
  pickHigherType _ (VConst _ Sort) = Sort
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
