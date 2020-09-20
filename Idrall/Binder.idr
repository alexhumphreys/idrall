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

data Bindr : Type -> Type where
     Lam : ty -> Bindr ty
     Pi : ty -> Bindr ty
     Let : ty -> Bindr ty

data RawExpr a
  = RLocal Name Nat
  | RLet Name (RawExpr a) (RawExpr a)
  | RPi Name (RawExpr a) (RawExpr a)
  | RLam Name (RawExpr a) (RawExpr a)
  | RApp (RawExpr a) (RawExpr a)
  | RType
  | RBool
  | RBoolLit Bool

data Expr : (ns : List Name) -> Type where
     ELocal : (n : Name) -> (idx : Nat) -> (p : IsVar n idx ns) -> Expr ns
     EBind : (n : Name) -> Bindr (Expr ns) -> (scope: Expr (n :: ns)) -> Expr ns
     EApp : Expr ns -> Expr ns -> Expr ns
     EType : Expr ns
     EBool : Expr ns
     EBoolLit : Bool -> Expr ns

data Env : (tm : List Name -> Type) -> List Name -> Type where
     Nil : Env tm []
     (::) : Bindr (tm vars) -> Env tm vars -> Env tm (x :: vars)

mutual
  data LocalEnv : List Name -> List Name -> Type where
       EmptyLE : LocalEnv free []
       AppendLE : Closure free -> LocalEnv free vars -> LocalEnv free (x :: vars)

  data Closure : List Name -> Type where
       MkClosure : {vars : _} ->
                   LocalEnv free vars ->
                   Env Expr free ->
                   Expr (vars ++ free) -> Closure free

mutual
  data Val : List Name -> Type where
       VBind : (x : Name) -> Bindr (Val vars) ->
               (Closure vars -> Val vars) -> Val vars
       VType : Val vars
       VBool : Val vars
       VBoolLit : Bool -> Val vars
       VNeutral : Ty vars -> Neutral vars -> Val vars

  Ty : List Name -> Type
  Ty vars = Val vars

  data Neutral : List Name -> Type where
       NLocal : (n : Name) -> (idx : Nat) -> (p : IsVar n idx ns) -> Neutral vars
       NApp : Neutral vars -> Normal vars -> Neutral vars

  data Normal : List Name -> Type where
       MkNormal : Ty vars -> Val vars -> Normal vars

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

checkScope : (ns : List Name) -> RawExpr a -> Either String (Expr ns)
checkScope ns (RLocal x k) =
  let scp = checkLocal x k ns in
      (case scp of
            (Left l) => Left "Scope error"
            (Right r) => Right (ELocal x k r))
checkScope ns (RLet x y z) = do
  y' <- checkScope ns y
  z' <- checkScope (x :: ns) z
  Right (EBind x (Let y') z')
checkScope ns (RPi x y z) = do
  y' <- checkScope ns y
  z' <- checkScope (x :: ns) z
  Right (EBind x (Pi y') z')
checkScope ns (RLam x y z) = do
  y' <- checkScope ns y
  z' <- checkScope (x :: ns) z
  Right (EBind x (Lam y') z')
checkScope ns RBool = Right EBool
checkScope ns (RBoolLit x) = Right (EBoolLit x)
checkScope ns (RApp x y) = do
  x' <- checkScope ns x
  y' <- checkScope ns y
  Right (EApp x' y')
checkScope ns RType = Right EType

mutual
  evalLocClosure : {free : _} ->
                   Env Expr free ->
                   Closure free ->
                   Val free
  evalLocClosure env (MkClosure locs' env' tm') =
    eval env' locs' tm'

  evalLocal : {free, vars : _} ->
              Env Expr free ->
              (idx : Nat) -> (p : IsVar name idx (vars ++ free)) ->
              LocalEnv free vars ->
              Val free
  evalLocal {vars = []} (x :: y) Z First EmptyLE = VBind (MkName ?foo_3) (Lam VType) ?foo_5
  evalLocal {vars = []} env (S k) (LaterMatch x) EmptyLE = ?foo_4
  evalLocal {vars = []} env idx (LaterNotMatch x) EmptyLE = ?foo_2
  evalLocal env Z prf (AppendLE x locs) = evalLocClosure env x
  evalLocal {vars = (x :: xs)} {free}
            env (S idx) (LaterMatch p) (AppendLE _ locs) = evalLocal env idx p locs
  evalLocal {vars = (x :: xs)} {free}
            env (S idx) (LaterNotMatch p) (AppendLE _ locs) = evalLocal env (S idx) p locs

  eval : {free, vars : _} ->
         Env Expr free -> LocalEnv free vars ->
         Expr (vars ++ free) -> Val free
  eval env locs (ELocal n idx p) = ?eval_rhs_1
  eval env locs (EBind n x scope) = ?eval_rhs_2
  eval env locs (EApp x y) = ?eval_rhs_3
  eval env locs EType = ?eval_rhs_4
  eval env locs EBool = ?eval_rhs_5
  eval env locs (EBoolLit x) = ?eval_rhs_6

ex1 : RawExpr ()
ex1 = RLet (MkName "x") (RBoolLit True) (RLocal (MkName "x") 0)

ex2 : RawExpr ()
ex2 = RLet (MkName "x") (RBoolLit True) (RLet (MkName "x") (RBoolLit False) (RLocal (MkName "x") 1))

ex3 : RawExpr ()
ex3 = RLet (MkName "x") (RBoolLit True)
      (RLet (MkName "y") (RBoolLit False)
        (RLet (MkName "f")
          (RLam (MkName "x") (RBool) (RLocal (MkName "x") 0))
        (RLocal (MkName "x") 0)))

emptyNames : List Name
emptyNames = []

partial
discarder : Either String (Expr ns) -> (Expr ns)
discarder x = case x of
                   (Left y) => ?discarder_rhs_1
                   (Right y) => y

partial
ex1S : (Expr Main.emptyNames)
ex1S = (discarder (checkScope emptyNames ex1))

partial
ex2S : (Expr Main.emptyNames)
ex2S = (discarder (checkScope emptyNames ex2))

partial
ex3S : (Expr Main.emptyNames)
ex3S = (discarder (checkScope emptyNames ex3))

--- ex1S = checkScope [] ex1

{-

mutual
  data Normal : Type where
       MkNormal : Ty -> Val -> Normal

  Ty : Type
  Ty = Val

  data Val : Type where
       VPi : (n : Name) -> Ty -> Closure ns -> Val
       VLam : (n : Name) -> Ty -> Closure ns -> Val
       VType : Val
       VBool : Val
       VBoolLit : Bool -> Val
       VNeutral : Ty -> Neutral -> Val

  data Env : (tm : Type) -> List Name -> Type where
       Nil : Env tm []
       (::) : (a : tm) -> Env tm ns -> Env tm (n :: ns)

  data Closure : List Name -> Type where
       MkClosure : (n : Name) ->
                   Env Val (n :: ns) ->
                   Expr ns a ->
                   Expr (n :: ns) a ->
                   Closure ns

  data Neutral : Type where
       NVar : Name -> Neutral
       NApp : Neutral -> Normal -> Neutral

-- eval
data Ctx
  = Def Ty Val
  | IsA Name Ty

mutual
  envLookup : (n : Name) -> (idx : Nat) -> (prf : IsVar n idx ns) -> (env : Env a ns) -> a
  envLookup n Z First (x :: y) = x
  envLookup n Z (LaterNotMatch p) (y :: z) = envLookup n Z p z
  envLookup n (S k) (LaterMatch p) (y :: z) = envLookup n k p z
  envLookup n (S k) (LaterNotMatch p) (y :: z) = envLookup n (S k) p z

  eval : (env : Env Val ns) -> Expr ns a -> Either String Val
  eval env (ELocal n k p) = Right (envLookup n k p env)
  eval env (ELet n x y) = do
    x' <- eval env x
    y' <- eval (x' :: env) y
    Right y'
  eval env (EPi n ty body) = do
    ty' <- eval env ty
    Right (VPi n ty' (MkClosure n (ty' :: env) ty body))
  eval env (ELam n ty body) = do
    ty' <- eval env ty
    Right (VLam n ty' (MkClosure n (ty' :: env) ty body))
  eval env (EApp x y) = do
    x' <- eval env x
    y' <- eval env y
    doApply x' y'
  eval env EType = Right VType
  eval env EBool = Right VBool
  eval env (EBoolLit x) = Right (VBoolLit x)

  doApply : Val -> Val -> Either String Val

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
