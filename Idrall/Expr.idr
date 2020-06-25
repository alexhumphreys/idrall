public export
Name : Type
Name = String

public export
Namespace : Type
Namespace = List (Name, Integer)
%name Namespace ns1, ns2, ns3

public export
data U = CType | Sort | Kind

export
Eq U where
  (==) CType CType = True
  (==) Sort Sort = True
  (==) Kind Kind = True
  (==) _ _ = False

export
Show U where
  show CType = "CType"
  show Sort = "Sort"
  show Kind = "Kind"
-- expressions

data ImportStatement
  = LocalFile String
  | EnvVar String

public export
data Expr a
  -- x
  = EVar Name
  | EConst U
  | EPi Name (Expr a) (Expr a)
  -- | Lam x A b ~ λ(x : A) -> b
  | ELam Name (Expr a) (Expr a)
  -- | > App f a ~ f a
  | EApp (Expr a) (Expr a)
  -- | > Let x Nothing r e ~ let x = r in e
  --   > Let x (Just t) r e ~ let x : t = r in e
  | ELet Name (Maybe (Expr a)) (Expr a) (Expr a)
  -- | > Annot x t ~ x : t
  | EAnnot (Expr a) (Expr a)
  -- | > x === y
  | EEquivalent (Expr a) (Expr a)
  -- | > assert : e
  | EAssert (Expr a)
  -- | > Bool ~ Bool
  | EBool
  -- | > BoolLit b ~ b
  | EBoolLit Bool
  -- | > BoolAnd x y ~ x && y
  | EBoolAnd (Expr a) (Expr a)
  -- | > Natural ~ Natural
  | ENatural
  -- | > NaturalLit n ~ n
  | ENaturalLit Nat
  -- | > NaturalIsZero ~ Natural/isZero
  | ENaturalIsZero (Expr a)
  -- | > EList a ~ List a
  | EList (Expr a)
  -- | > EList (Some e) [e', ...] ~ [] : List a
  | EListLit (Maybe (Expr a)) (List (Expr a))
  -- | > x # y
  | EListAppend (Expr a) (Expr a)

export
Show (Expr a) where
  show (EVar x) = "(EVar " ++ show x ++ ")"
  show (EConst x) = "(EConst " ++ show x ++ ")"
  show (EPi x y z) = "(EPi " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
  show (ELam x y z) = "(ELam " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
  show (EApp x y) = "(EApp " ++ show x ++ " " ++ show y ++ ")"
  show (ELet x y z w) = "(ELet " ++ show x ++ " " ++ show y ++ " " ++ show z ++ " " ++ show w ++ ")"
  show (EAnnot x y) = "(EAnnot " ++ show x ++ " " ++ show y ++ ")"
  show (EEquivalent x y) = "(EEquivalent " ++ show x ++ " " ++ show y ++ ")"
  show (EAssert x) = "(EAssert " ++ show x ++ ")"
  show EBool = "EBool"
  show (EBoolLit False) = "(EBoolLit False)"
  show (EBoolLit True) = "(EBoolLit True)"
  show (EBoolAnd x y) = "(EBoolAnd " ++ show x ++ " " ++ show y ++ ")"
  show ENatural = "ENatural"
  show (ENaturalLit k) = "(ENaturalLit " ++ show k ++ ")"
  show (ENaturalIsZero x) = "(ENaturalIsZero " ++ show x ++ ")"
  show (EList x) = "(EList " ++ show x ++ ")"
  show (EListLit Nothing xs) = "(EListLit Nothing " ++ show xs ++ ")"
  show (EListLit (Just x) xs) = "(EListLit (Just " ++ show x ++ ") " ++ show xs ++ ")"
  show (EListAppend x y) = "(EListAppend " ++ show x ++ " " ++ show y ++ ")"

data Error

data IOEither a b
 = MkIOEither (IO (Either a b))

Functor (IOEither a) where
  map func (MkIOEither x) = MkIOEither (map (map func) x)

Applicative (IOEither a) where
  pure x = MkIOEither (pure (pure x))
  (<*>) (MkIOEither x) (MkIOEither y) = MkIOEither (liftA2 (<*>) x y)

Monad (IOEither a) where
  (>>=) (MkIOEither x) f = MkIOEither (do x' <- x
                                          (case x' of
                                                (Left l) => pure (Left l)
                                                (Right r) => let MkIOEither g = f r in
                                                                 g))
  join x = x >>= id

mutual
  resolve : Expr ImportStatement -> IOEither Error (Expr Void)
  resolve e@(EVar x) = pure e
  resolve e@(EConst x) = pure e
  resolve (EPi x y z) = do
    y' <- resolve y
    z' <- resolve z
    pure (EPi x y' z')
  resolve (ELam x y z) = do
    y' <- resolve y
    z' <- resolve z
    pure (ELam x y' z')
  resolve (EApp x y) = do
    x' <- resolve x
    y' <- resolve y
    pure (EApp x' y')
  resolve (ELet x Nothing z w) = do
    z' <- resolve z
    w' <- resolve w
    pure (ELet x Nothing z' w')
  resolve (ELet x (Just y) z w) = do
    y' <- resolve y
    z' <- resolve z
    w' <- resolve w
    pure (ELet x (Just y') z' w')
  resolve (EAnnot x y) = do
    x' <- resolve x
    y' <- resolve y
    pure (EAnnot x' y')
  resolve (EEquivalent x y) = do
    x' <- resolve x
    y' <- resolve y
    pure (EEquivalent x' y')
  resolve (EAssert x) = do
    x' <- resolve x
    pure (EAssert x')
  resolve e@EBool = pure e
  resolve e@(EBoolLit x) = pure e
  resolve (EBoolAnd x y) = do
    x' <- resolve x
    y' <- resolve y
    pure (EBoolAnd x' y')
  resolve e@ENatural = pure e
  resolve e@(ENaturalLit k) = pure e
  resolve (ENaturalIsZero x) = do
    x' <- resolve x
    pure (ENaturalIsZero x')
  resolve (EList x) = do
    x' <- resolve x
    pure (EList x')
  resolve (EListLit Nothing xs) = do
    xs' <- resolveList xs
    pure (EListLit Nothing xs')
  resolve (EListLit (Just x) xs) = do
    x' <- resolve x
    xs' <- resolveList xs
    pure (EListLit (Just x') xs')
  resolve (EListAppend x y) = do
    x' <- resolve x
    y' <- resolve y
    pure (EListAppend x' y')

  resolveList : List (Expr ImportStatement) ->
                 IOEither Error (List (Expr Void))
  resolveList [] = MkIOEither (pure (Right []))
  resolveList (x :: xs) =
    let rest = resolveList xs in
    do rest' <- rest
       x' <- resolve x
       MkIOEither (pure (Right (x' :: rest')))
