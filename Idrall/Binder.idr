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
  data Normal : List Name -> Type where
       MkNormal : Ty vars -> Val vars -> Normal vars

  Ty : List Name -> Type
  Ty vars = Val vars

  data Val : List Name -> Type where
       VPi : (n : Name) -> Ty vars -> Closure (n :: vars) -> Val vars
       VLam : (n : Name) -> Ty vars -> Closure (n :: vars) -> Val vars
       VType : Val vars
       VBool : Val vars
       VBoolLit : Bool -> Val vars
       VNeutral : Ty vars -> Neutral vars -> Val vars

  data Env : (tm : List Name -> Type) -> List Name -> Type where
       Nil : Env tm []
       (::) : (a : tm ns) -> Env tm ns -> Env tm (n :: ns)

  data Closure : List Name -> Type where
       MkClosure : (n : Name) ->
                   Env Val (ns) ->
                   Expr ns a ->
                   Expr (n :: ns) a ->
                   Closure ns

  data Neutral : List Name -> Type where
       NVar : Name -> Neutral vars
       NApp : Neutral vars -> Normal vars -> Neutral vars

-- eval
data Ctx
  = Def (Ty vars) (Val vars)
  | IsA Name (Ty vars)

weaken : Val ns -> Val (n :: ns)

mutual
  envLookup : (n : Name) -> (idx : Nat) -> (prf : IsVar n idx ns) -> (env : Env Val ns) -> Val ns
  {- envLookup n Z First (x :: y) = weaken x
  envLookup n Z (LaterNotMatch p) (y :: z) = weaken (envLookup n Z p z)
  envLookup n (S k) (LaterMatch p) (y :: z) = weaken (envLookup n k p z)
  envLookup n (S k) (LaterNotMatch p) (y :: z) = weaken (envLookup n (S k) p z) -}

  eval : (env : Env (\os => Val (os ++ ns)) ms) -> Expr ns a -> Either String (Val ns)
  eval env (ELocal n k p) = ?eeee -- Right (envLookup n k p env)
  eval env (ELet n x y) = do
    x' <- eval env x
    y' <- eval (x' :: env) y
    Right ?foo
    -- Right y'
  eval env (EPi n ty body) = do
    ty' <- eval env ty
    --Right (VPi n ty' (MkClosure n (ty' :: env) ty body))
    ?bar1
  eval env (ELam n ty body) = do
    ty' <- eval env ty
    ?bar2
    --Right (VLam n ty' (MkClosure n (ty' :: env) ty body))
  eval env (EApp x y) = do
    x' <- eval env x
    y' <- eval env y
    doApply x' y'
  eval env EType = Right VType
  eval env EBool = Right VBool
  eval env (EBoolLit x) = Right (VBoolLit x)

  doApply : Val vars -> Val vars -> Either String (Val vars)

{-
  mkEnv : Env Ctx ns -> Env Val ns
  mkEnv [] = []
  mkEnv ((IsA y z) :: x) = z :: mkEnv x
  mkEnv ((Def _ z) :: x) = z :: mkEnv x

  synth : (ctx : Env Ctx ns) -> Expr ns a -> Either String Val
  synth ctx (ELocal n idx p) =
    let v = envLookup n idx p ctx in
        (case v of
              (Def x y) => Right x
              (IsA x y) => Right y)
  synth ctx (ELet n x y) = ?synth_rhs_2
  synth ctx (EPi n x y) = ?synth_rhs_1
  synth ctx (ELam n ty body) = do
    tyV <- eval (mkEnv ctx) ty
    ?synth_rhs_3
  synth ctx (EApp x y) = ?synth_rhs_4
  synth ctx EType = ?synth_rhs_7
  synth ctx EBool = ?synth_rhs_5
  synth ctx (EBoolLit x) = ?synth_rhs_6
-}
