%hide Language.Reflection.Var

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
  = RLocal String Nat
  | RLet String (RawExpr a) (RawExpr a)
  | RLam String (RawExpr a) (RawExpr a)
  | RBool
  | RBoolLit Bool

data Expr : (ns : List Name) -> a -> Type where
     ELocal : (n : Name) -> (idx : Nat) -> (p : IsVar n idx ns) -> Expr ns a
     ELet : (n : Name) -> (Expr ns a) -> (Expr (n :: ns) a) -> Expr ns a
     ELam : (n : Name) -> (Expr ns a) -> (Expr (n :: ns) a) -> Expr ns a
     EBool : Expr ns a
     EBoolLit : Bool -> Expr ns a

inversion : IsVar n (S k) (v :: vs) -> IsVar n k vs
inversion x = ?inversion_rhs

recurse : (r : IsVar x k xs) -> IsVar x (S k) (x :: xs)
recurse First = LaterMatch First
recurse r = LaterMatch r

checkLocal : (n : Name) -> (k : Nat) -> (ns : List Name) -> Either String (IsVar n k ns)
checkLocal n Z [] = Left "Not in empty"
checkLocal n Z (x :: xs) = case decEq n x of
                                (Yes Refl) => Right First
                                (No contra) => Left ?checkLocal_rhs_3
checkLocal n (S k) [] = Left "Definitely not in empty"
checkLocal n (S k) (x :: xs) with (decEq n x)
  checkLocal x (S k) (x :: xs) | (Yes Refl) =
    let rest = checkLocal x k xs in
    case rest of
         (Left l) => Left ?checkLocal_rhs_4
         (Right r) => Right (recurse r)
  checkLocal n (S k) (x :: xs) | (No contra) =
    let rest = checkLocal n (S k) xs in
        (case rest of
              (Left l) => Left ?foo_1
              (Right r) => Right (LaterNotMatch r))

checkScope : (ns : List Name) -> RawExpr a -> Either String (Expr ns a)
checkScope ns (RLocal x k) = ?checkScope_rhs_1
checkScope ns (RLet x y z) = ?checkScope_rhs_2
checkScope ns (RLam x y z) = ?checkScope_rhs_3
checkScope ns RBool = ?checkScope_rhs_4
checkScope ns (RBoolLit x) = ?checkScope_rhs_5
