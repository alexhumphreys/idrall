module Idrall.Resolve

import Idrall.Error
import Idrall.Expr
import Idrall.IOEither
import Idrall.Parser

liftEither : Either e a -> IOEither e a
liftEither = MkIOEither . pure

liftIO : IO a -> IOEither e a
liftIO = MkIOEither . map Right

mapErr : (e -> e') -> IOEither e a -> IOEither e' a
mapErr f (MkIOEither x) = MkIOEither (do
  x' <- x
  (case x' of
        (Left l) => pure (Left (f l))
        (Right r) => pure (Right r)))

fileErrorHandler : FileError -> Error
fileErrorHandler x = ReadFileError (show x)

readFile' : String -> IOEither Error String
readFile' x =
  let c = MkIOEither (readFile x)
      contents = mapErr (fileErrorHandler) c in
  contents

parseErrorHandler : String -> Error
parseErrorHandler x = ErrorMessage (x)

mutual
  canonicalFilePath : FilePath -> String -- TODO finish properly
  canonicalFilePath (Relative x) = x
  canonicalFilePath (Absolute x) = x

  resolveLocalFile : FilePath -> IOEither Error (Expr Void)
  resolveLocalFile x = go (canonicalFilePath x)
    where
    go : (x : String) -> IOEither Error (Expr Void)
    go x = do
      c <- readFile' x
      e <- mapErr (parseErrorHandler) (liftEither (parseExpr c))
      resolve e

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
  resolve (EEmbed (Raw (LocalFile x))) = resolveLocalFile x
  resolve (EEmbed (Raw (EnvVar x))) = MkIOEither (pure (Left (ErrorMessage "TODO not implemented")))
  resolve (EEmbed (Resolved x)) = MkIOEither (pure (Left (ErrorMessage "Already resolved")))

  resolveList : List (Expr ImportStatement) ->
                 IOEither Error (List (Expr Void))
  resolveList [] = MkIOEither (pure (Right []))
  resolveList (x :: xs) =
    let rest = resolveList xs in
    do rest' <- rest
       x' <- resolve x
       MkIOEither (pure (Right (x' :: rest')))
