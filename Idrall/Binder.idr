import Decidable.Equality

data Name : Type where
     MkName : String -> Name

nameNotEq : (contra : (x = y) -> Void) -> (MkName x = MkName y) -> Void
nameNotEq contra Refl = contra Refl

DecEq Name where
  decEq (MkName x) (MkName y) with (decEq x y)
    decEq (MkName y) (MkName y) | (Yes Refl) = Yes Refl
    decEq (MkName x) (MkName y) | (No contra) = No (nameNotEq contra)

data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     LaterMatch : IsVar n k (ns) -> IsVar n (S k) (n :: ns)
     LaterNotMatch : IsVar n k ns -> IsVar n k (m :: ns)

data Var : List Name -> Type where
     MkVar : (n : Name) -> (k : Nat) -> IsVar n k ns -> Var ns

data RawExpr a
  = RLocal Name Nat
  | RLet Name (RawExpr a) (RawExpr a)
  | RPi Name (RawExpr a) (RawExpr a)
  | RLam Name (RawExpr a) (RawExpr a)
  | RApp (RawExpr a) (RawExpr a)
  | RType
  | RBool
  | RBoolLit Bool

data Expr : (ns : List Name) -> a -> Type where
     ELocal : (n : Name) -> (idx : Nat) -> (p : IsVar n idx ns) -> Expr ns a
     ELet : (n : Name) -> (Expr ns a) -> (Expr (n :: ns) a) -> Expr ns a
     EPi : (n : Name) -> (Expr ns a) -> (Expr (n :: ns) a) -> Expr ns a
     ELam : (n : Name) -> (Expr ns a) -> (Expr (n :: ns) a) -> Expr ns a
     EApp : Expr ns a -> Expr ns a -> Expr ns a
     EType : Expr ns a
     EBool : Expr ns a
     EBoolLit : Bool -> Expr ns a

checkLocal : (n : Name) -> (k : Nat) -> (ns : List Name) -> Either String (IsVar n k ns)
checkLocal n Z [] = Left "Not in empty"
checkLocal n Z (x :: xs) with (decEq n x)
  checkLocal x Z (x :: xs) | (Yes Refl) = Right First
  checkLocal n Z (x :: xs) | (No contra) =
    let rest = checkLocal n Z xs in
    (case rest of
          (Left l) => Left "Not in list at all"
          (Right r) => Right (LaterNotMatch r))
checkLocal n (S k) [] = Left "Definitely not in empty"
checkLocal n (S k) (x :: xs) with (decEq n x)
  checkLocal x (S k) (x :: xs) | (Yes Refl) =
    let rest = checkLocal x k xs in
    case rest of
         (Left l) => Left "Match but not in rest of list"
         (Right r) => Right (LaterMatch r)
  checkLocal n (S k) (x :: xs) | (No contra) =
    let rest = checkLocal n (S k) xs in
        (case rest of
              (Left l) => Left "No match and not in rest of list"
              (Right r) => Right (LaterNotMatch r))

checkScope : (ns : List Name) -> RawExpr a -> Either String (Expr ns a)
checkScope ns (RLocal x k) =
  let scp = checkLocal x k ns in
      (case scp of
            (Left l) => Left "Scope error"
            (Right r) => Right (ELocal x k r))
checkScope ns (RLet x y z) = do
  y' <- checkScope ns y
  z' <- checkScope (x :: ns) z
  Right (ELet x y' z')
checkScope ns (RPi x y z) = do
  y' <- checkScope ns y
  z' <- checkScope (x :: ns) z
  Right (EPi x y' z')
checkScope ns (RLam x y z) = do
  y' <- checkScope ns y
  z' <- checkScope (x :: ns) z
  Right (ELam x y' z')
checkScope ns RBool = Right EBool
checkScope ns (RBoolLit x) = Right (EBoolLit x)
checkScope ns (RApp x y) = do
  x' <- checkScope ns x
  y' <- checkScope ns y
  Right (EApp x' y')
checkScope ns RType = Right EType

mutual
  data Value : List Name -> Type where
       VPi : (n : Name) -> Ty vars -> Closure n (vars) -> Value vars
       -- VHPi : (n : Name) -> Val vars -> (Val vars -> Val (n :: vars)) -> Val vars
       VLam : (n : Name) -> Ty vars -> Closure n (vars) -> Value vars
       VType : Value vars
       VBool : Value vars
       VBoolLit : Bool -> Value vars
       VNeutral : Neutral vars -> Value vars

  data Normal : List Name -> Type where
       MkNormal : Ty vars -> Value vars -> Normal vars

  Ty : List Name -> Type
  Ty vars = Value vars

  data LocalEnv : List Name -> List Name -> Type where
       EmptyLE : LocalEnv ns []
       AppendLE : Value ns -> LocalEnv ns ms -> LocalEnv ns (n :: ms)

  data VHPiLam : List Name -> Type where
       VHListFold : Value vars -> Value vars -> Value vars -> Value vars -> Value vars -> VHPiLam vars
       VHNaturalIsZero : Value vars -> VHPiLam vars

  data Env : (tm : List Name -> Type) -> List Name -> Type where
       Empty : Env tm []
       Skip : (n : Name) -> Env tm ns -> Env tm (n :: ns)
       Extend : (a : tm ns) -> Env tm ns -> Env tm (n :: ns)

  data Env' : (tm : List Name -> Type) -> List Name -> Type where
       Empty' : Env' tm []
       Skip' : (n : Name) -> Env' tm ns -> Env' tm (n :: ns)
       Extend' : (a : tm ns) -> Env' tm ns -> Env' tm (n :: ns)

  data Closure : Name -> List Name -> Type where
       MkClosure : {mss: _} ->
                   (n : Name) ->
                   LocalEnv ns mss ->
                   Env Value (ns) ->
                   Expr (n :: (mss ++ ns)) () ->
                   Closure n ns

  data Neutral : List Name -> Type where
       NVar : Name -> Neutral vars
       NApp : Neutral vars -> Normal vars -> Neutral vars

-- eval
data Cxt : List Name -> Type where
  Def : (Ty vars) -> (Value vars) -> Cxt vars
  IsA : Name -> (Ty vars) -> Cxt vars

data Types = TEmpty
           | TBind Types Name (Value ns)

record Cxt' where
  constructor MkCxt'
  values : Env' Value ns
  types  : Types

interface Weaken (tm : List Name -> Type) where
  weaken : {n, vars : _} -> tm vars -> tm (n :: vars)
  weakenNs : {vars : _} -> (ns : List Name) -> tm vars -> tm (ns ++ vars)

  weakenNs [] t = t
  weakenNs (n :: ns) t = weaken (weakenNs ns t)

  weaken = weakenNs [_]

{-
Weaken Expr where
  weakenNs ns tm = insertNames {outer = []} ns tm
  -}

mutual
  weakenExpr : {ns : _} -> (n : _) -> Expr ns () -> Expr (n :: ns) ()
  weakenExpr n x = weakenInner {mss=[]} x

  weakenLocs : {n:_} -> LocalEnv ns ms -> LocalEnv (n :: ns) ms
  weakenLocs EmptyLE = EmptyLE
  weakenLocs (AppendLE x y) = AppendLE (weakenVal x) (weakenLocs y)

  weakenEnv : {n:_} -> Env Value ns -> Env Value (n :: ns) -- TODO not sure about this, or weakenClosure
  weakenEnv e = Skip n e

  weakenVar : {idx:_} -> (mss : List Name) -> IsVar y idx (mss ++ ns) -> IsVar y idx (mss ++ (n :: ns))
  weakenVar [] x = LaterNotMatch x
  weakenVar (_ :: xs) First = First
  weakenVar (_ :: xs) (LaterMatch x) = LaterMatch (weakenVar xs x)
  weakenVar (y :: xs) (LaterNotMatch x) = LaterNotMatch (weakenVar xs x)

  weakenInner : {n,mss : _} -> Expr (mss ++ ns) () -> Expr (mss ++ (n :: ns)) ()
  weakenInner (ELocal y idx p) with (decEq n y)
    -- TODO no (S idx)?? maybe y is in mss then wouldn't need the S?
    weakenInner (ELocal n idx p) | (Yes Refl) = ELocal n idx (weakenVar mss p)
    weakenInner (ELocal y idx p) | (No contra) = ELocal y idx (weakenVar mss p)
  weakenInner (ELet y z w) = ELet y (weakenInner z) (weakenInner {mss=(y::mss)} w)
  weakenInner (EPi y z w) = EPi y (weakenInner z) (weakenInner {mss=(y::mss)} w)
  weakenInner (ELam y z w) = ELam y (weakenInner z) (weakenInner {mss=(y::mss)} w)
  weakenInner (EApp y z) = EApp (weakenInner y) (weakenInner z)
  weakenInner EType = EType
  weakenInner EBool = EBool
  weakenInner (EBoolLit y) = EBoolLit y

  weakenClosure : {x,n:_} -> Value ns -> Closure x ns -> Closure x (n :: ns)
  weakenClosure ty (MkClosure {mss} x locs env body) =
    MkClosure x (weakenLocs locs) (weakenEnv env) (weakenInner {mss=(x::mss)} body)

  weakenNeutral : {n:_} -> Neutral ns -> Neutral (n :: ns)
  weakenNeutral (NVar x) = NVar x
  weakenNeutral (NApp x y) = NApp (weakenNeutral x) (weakenNormal y)

  weakenNormal : {n:_} -> Normal ns -> Normal (n :: ns)
  weakenNormal (MkNormal x y) = MkNormal (weakenVal x) (weakenVal y)

  weakenVHPi : {n:_} ->
               (x : Name) ->
               (Value ns -> Value (x :: ns)) ->
               (Value (n :: ns) -> Value (x :: (n :: ns)))
  weakenVHPi x f = ?weakenVHPi_rhs

  weakenVal : {n:_} -> Value ns -> Value (n :: ns)
  weakenVal (VPi x ty z) = VPi x (weakenVal ty) (weakenClosure ty z)
  -- weakenVal (VHPi x ty f) = VHPi x (weakenVal ty) (weakenVHPi x f)
  weakenVal (VLam x ty z) = VLam x (weakenVal ty) (weakenClosure ty z)
  weakenVal VType = VType
  weakenVal VBool = VBool
  weakenVal (VBoolLit x) = VBoolLit x
  weakenVal (VNeutral y) = VNeutral (weakenNeutral y)

mutual

  ll : {n,ns,ms : _} -> IsVar n idx (ms ++ ns) -> LocalEnv ns ms -> Env Value ns -> Value ns
  ll {ms = []} First EmptyLE (Extend a env) = weakenVal a
  ll {ms = []} First EmptyLE (Skip n env) =  VNeutral $ NVar n -- weakenVal (ll First EmptyLE (weakenEnv env))
  ll {ms = []} (LaterMatch p) EmptyLE (Extend _ env) = weakenVal (ll p EmptyLE env)
  ll {ms = []} (LaterNotMatch p) EmptyLE (Extend _ env) = weakenVal (ll p EmptyLE env)
  ll {ms = []} (LaterMatch p) EmptyLE (Skip _ env) = weakenVal (ll p EmptyLE env)
  ll {ms = []} (LaterNotMatch p) EmptyLE (Skip _ env) = weakenVal (ll p EmptyLE env)
  ll First (AppendLE y w) env = y
  ll (LaterMatch p) (AppendLE y w) env = ll p w env
  ll (LaterNotMatch p) (AppendLE y w) env = ll p w env

  eval : {ns,ms : List Name} -> (env : Env Value ns) -> (locs : LocalEnv ns ms) -> Expr (ms ++ ns) () -> Either String (Value ns)
  eval env locs (ELocal n idx p) = Right (ll p locs env)
  eval env locs (ELet n x y) = do
    x' <- eval env locs x
    y' <- eval env (AppendLE x' locs) y
    Right y'
  eval env locs (EPi n ty body) = do
    ty' <- eval env locs ty
    Right (VPi n ty' (MkClosure n locs (env) body))
  eval env locs (ELam n ty body) = do
    ty' <- eval env locs ty
    Right (VLam n ty' (MkClosure n locs (env) body))
  eval env locs (EApp x y) = do
    x' <- eval env locs x
    y' <- eval env locs y
    doApply x' y'
  eval env locs EType = Right VType
  eval env locs EBool = Right VBool
  eval env locs (EBoolLit x) = Right (VBoolLit x)

  evalClosure : {ns:_} -> Closure n ns -> Value ns -> Either String (Value ns)
  evalClosure (MkClosure n locs env body) arg =
      eval env (AppendLE arg locs) body

  doApply : {ns : _} -> Value ns -> Value ns -> Either String (Value ns)
  doApply (VLam n ty closure) arg = do
    -- eval env' (AppendLE arg locs') body
    evalClosure closure arg
  doApply f a = ?doApply_rhs_11


ex1 : Expr [] ()
ex1 = ELet (MkName "x") (EBoolLit True) (ELocal (MkName "x") 0 First)

ex2 : Expr [] ()
ex2 = ELet (MkName "x") (EBoolLit True)
        (ELet (MkName "y") (EBoolLit False)
          (ELocal (MkName "x") 0 (LaterNotMatch First))
        )

ex3 : Expr [] ()
ex3 = ELet (MkName "x") (EBoolLit True)
        (ELet (MkName "f")
          (ELam (MkName "y") (EBool)
            (ELocal (MkName "y") 0 (First))
          )
          (EApp (ELocal (MkName "f") 0 (First))
                (ELocal (MkName "x") 0 (LaterNotMatch First))
          )
        )

mkEnv : Env Cxt ns -> Env Value ns
mkEnv Empty = Empty
mkEnv (Skip n env) = Skip n (mkEnv env)
mkEnv (Extend (IsA y z) x) = Extend z (mkEnv x)
mkEnv (Extend (Def _ z) x) = Extend z (mkEnv x)

freshen : List Name -> Name -> Name

readBackTyped : {ns:_} -> (cxt : Env Cxt ns) -> (Value ns) -> (Value ns) -> Either String (Expr ns ())
readBackTyped cxt (VPi n dom ran) fun =
  let n' = freshen ns n
      nVal = VNeutral (NVar n)
      cxt' = Extend (IsA n dom) cxt
  in
  do ty' <- evalClosure ran nVal
     eTy <- readBackTyped cxt (VType) (ty') -- TODO should be cxt or cxt'?
     v' <- doApply fun nVal
     body <- readBackTyped cxt' (weakenVal ty') (weakenVal v')
     Right (ELam n eTy body)
readBackTyped cxt (VLam n x z) y = ?readBackTyped_rhs_2
readBackTyped cxt VType VBool = Right EBool
readBackTyped cxt VBool y = ?readBackTyped_rhs_4
readBackTyped cxt (VBoolLit x) y = ?readBackTyped_rhs_5
readBackTyped cxt (VNeutral z) y = ?readBackTyped_rhs_6
readBackTyped cxt x y = ?readBackTyped_rhs_7

synth : {ns:_} -> (cxt : Env Cxt ns) -> Expr ns () -> Either String (Value ns)
synth cxt (ELocal n idx p) = ?foo
  --let v = envLookup n idx p cxt in
      --(case v of
            --(Def x y) => Right x
            --(IsA x y) => Right y)
synth cxt (ELet n x y) = ?synth_rhs_2
synth cxt (EPi n x y) = ?synth_rhs_1
synth cxt (ELam n ty body) = do
  tyV <- eval (mkEnv cxt) EmptyLE ty
  bodyTy <- synth (Extend (IsA n tyV) cxt) body
  _ <- readBackTyped cxt (VType) tyV
  _ <- readBackTyped (Extend (IsA n tyV) cxt) (VType) bodyTy
  Right (VPi n tyV (MkClosure n EmptyLE (mkEnv cxt) body))
synth cxt (EApp x y) = ?synth_rhs_4
synth cxt EType = ?synth_rhs_7
synth cxt EBool = ?synth_rhs_5
synth cxt (EBoolLit x) = ?synth_rhs_6
