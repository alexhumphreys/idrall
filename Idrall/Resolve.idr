module Idrall.Resolve

import Idrall.Error
import Idrall.Expr
import Idrall.IOEither
import Idrall.Parser
import Idrall.Path

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

fileErrorHandler : String -> FileError -> Error
fileErrorHandler x y = ReadFileError (show y ++ " " ++ x)

readFile' : String -> IOEither Error String
readFile' x =
  let c = MkIOEither (readFile x)
      contents = mapErr (fileErrorHandler x) c in
  contents

parseErrorHandler : String -> Error
parseErrorHandler x = ErrorMessage (x)

nextCurrentPath : (current : Maybe Path) -> (next : Path) -> Path
nextCurrentPath (Just (Home xs)) (Relative ys) = Home (xs ++ ys)
nextCurrentPath (Just (Absolute xs)) (Relative ys) = Absolute (xs ++ ys)
nextCurrentPath (Just (Relative xs)) (Relative ys) = Relative (xs ++ ys)
nextCurrentPath _ p = p

combinePaths : Maybe FilePath -> FilePath -> FilePath
combinePaths Nothing y = y
combinePaths (Just (MkFilePath pathX fileNameX)) (MkFilePath pathY fileNameY) =
  let nextPath = nextCurrentPath (Just pathX) pathY
  in
  MkFilePath nextPath fileNameY

mutual
  canonicalFilePath : FilePath -> String -- TODO finish properly
  canonicalFilePath x = filePathForIO x

  resolveLocalFile : (current : Maybe FilePath) -> (next : FilePath) -> IOEither Error (Expr Void)
  resolveLocalFile w x =
    let combinedFilePaths = combinePaths w x in
        go combinedFilePaths
    where
    go : FilePath -> IOEither Error (Expr Void)
    go y = do
      c <- readFile' (canonicalFilePath y)
      e <- mapErr (parseErrorHandler) (liftEither (parseExpr c))
      resolve (Just y) e

  export
  resolve : Maybe FilePath -> Expr ImportStatement -> IOEither Error (Expr Void)
  resolve p e@(EVar x) = pure e
  resolve p e@(EConst x) = pure e
  resolve p (EPi x y z) = do
    y' <- resolve p y
    z' <- resolve p z
    pure (EPi x y' z')
  resolve p (ELam x y z) = do
    y' <- resolve p y
    z' <- resolve p z
    pure (ELam x y' z')
  resolve p (EApp x y) = do
    x' <- resolve p x
    y' <- resolve p y
    pure (EApp x' y')
  resolve p (ELet x Nothing z w) = do
    z' <- resolve p z
    w' <- resolve p w
    pure (ELet x Nothing z' w')
  resolve p (ELet x (Just y) z w) = do
    y' <- resolve p y
    z' <- resolve p z
    w' <- resolve p w
    pure (ELet x (Just y') z' w')
  resolve p (EAnnot x y) = do
    x' <- resolve p x
    y' <- resolve p y
    pure (EAnnot x' y')
  resolve p (EEquivalent x y) = do
    x' <- resolve p x
    y' <- resolve p y
    pure (EEquivalent x' y')
  resolve p (EAssert x) = do
    x' <- resolve p x
    pure (EAssert x')
  resolve p e@EBool = pure e
  resolve p e@(EBoolLit x) = pure e
  resolve p (EBoolAnd x y) = do
    x' <- resolve p x
    y' <- resolve p y
    pure (EBoolAnd x' y')
  resolve p e@ENatural = pure e
  resolve p e@(ENaturalLit k) = pure e
  resolve p (ENaturalIsZero x) = do
    x' <- resolve p x
    pure (ENaturalIsZero x')
  resolve p (EList x) = do
    x' <- resolve p x
    pure (EList x')
  resolve p (EListLit Nothing xs) = do
    xs' <- resolveList p xs
    pure (EListLit Nothing xs')
  resolve p (EListLit (Just x) xs) = do
    x' <- resolve p x
    xs' <- resolveList p xs
    pure (EListLit (Just x') xs')
  resolve p (EListAppend x y) = do
    x' <- resolve p x
    y' <- resolve p y
    pure (EListAppend x' y')
  resolve p (EEmbed (Raw (LocalFile x))) = resolveLocalFile p x
  resolve p (EEmbed (Raw (EnvVar x))) = MkIOEither (pure (Left (ErrorMessage "TODO not implemented")))
  resolve p (EEmbed (Resolved x)) = MkIOEither (pure (Left (ErrorMessage "Already resolved")))

  resolveList : Maybe FilePath -> List (Expr ImportStatement) ->
                 IOEither Error (List (Expr Void))
  resolveList p [] = MkIOEither (pure (Right []))
  resolveList p (x :: xs) =
    let rest = resolveList p xs in
    do rest' <- rest
       x' <- resolve p x
       MkIOEither (pure (Right (x' :: rest')))
