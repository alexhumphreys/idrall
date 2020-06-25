module Idrall.Resolve

import Idrall.Error
import Idrall.Expr
import Idrall.IOEither

mutual
  export
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
