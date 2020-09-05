%hide Language.Reflection.Var

data Name : Type where
     MkName : String -> Name

data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     LaterMatch : IsVar n k (ns) -> IsVar n (S k) (n :: ns)
     LaterNotMatch : IsVar n k ns -> IsVar n k (m :: ns)

data Var : List Name -> Type where
     MkVar : (n : Name) -> (k : Nat) -> IsVar n k ns -> Var ns

data RawExpr a
  = RLet String (RawExpr a) (RawExpr a)
  | RLam String (RawExpr a) (RawExpr a)
  | RNat
  | RNatLit Nat

data Expr a
  = ELet (Var vs) (RawExpr a) (RawExpr a)
  | ELam (Var vs) (RawExpr a) (RawExpr a)
  | ENat
  | ENatLit Nat
