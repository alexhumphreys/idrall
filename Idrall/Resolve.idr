module Idrall.Resolve

import Idrall.Error
import Idrall.Expr
import Idrall.IOEither
import Idrall.Parser
import Idrall.Path

liftEither : Either e a -> IOEither e a
liftEither = MkIOEither . pure

mapErr : (e -> e') -> IOEither e a -> IOEither e' a
mapErr f (MkIOEither x) = MkIOEither (do
  x' <- x
  (case x' of
        (Left l) => pure (Left (f l))
        (Right r) => pure (Right r)))

parseErrorHandler : String -> Error
parseErrorHandler x = ErrorMessage (x)

fileErrorHandler : String -> FileError -> Error
fileErrorHandler x y = ReadFileError (show y ++ " " ++ x)

readFile' : String -> IOEither Error String
readFile' x =
  let c = MkIOEither (readFile x)
      contents = mapErr (fileErrorHandler x) c in
  contents

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

canonicalFilePath : FilePath -> String -- TODO finish properly
canonicalFilePath x = filePathForIO x

alreadyImported : List FilePath -> FilePath -> Either Error () -- TODO check is correct
alreadyImported xs x = case elem x xs of
                            False => Right ()
                            True => Left (CyclicImportError ((show x) ++ " in " ++ (show xs)))

mutual
  resolveLocalFile : (history : List FilePath) -> (current : Maybe FilePath) -> (next : FilePath) -> IOEither Error (Expr Void)
  resolveLocalFile h current next =
    let combinedFilePaths = combinePaths current next in
        go combinedFilePaths
    where
    go : FilePath -> IOEither Error (Expr Void)
    go p = do
      liftEither (alreadyImported h (normaliseFilePath p))
      str <- readFile' (canonicalFilePath p)
      expr <- mapErr (parseErrorHandler) (liftEither (parseExpr str))
      resolve (normaliseFilePath p :: h) (Just p) expr

  export
  resolve : (history : List FilePath) -> Maybe FilePath -> Expr ImportStatement -> IOEither Error (Expr Void)
  resolve h p e@(EVar x) = pure e
  resolve h p e@(EConst x) = pure e
  resolve h p (EPi x y z) = do
    y' <- resolve h p y
    z' <- resolve h p z
    pure (EPi x y' z')
  resolve h p (ELam x y z) = do
    y' <- resolve h p y
    z' <- resolve h p z
    pure (ELam x y' z')
  resolve h p (EApp x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EApp x' y')
  resolve h p (ELet x Nothing z w) = do
    z' <- resolve h p z
    w' <- resolve h p w
    pure (ELet x Nothing z' w')
  resolve h p (ELet x (Just y) z w) = do
    y' <- resolve h p y
    z' <- resolve h p z
    w' <- resolve h p w
    pure (ELet x (Just y') z' w')
  resolve h p (EAnnot x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EAnnot x' y')
  resolve h p (EEquivalent x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EEquivalent x' y')
  resolve h p (EAssert x) = do
    x' <- resolve h p x
    pure (EAssert x')
  resolve h p e@EBool = pure e
  resolve h p e@(EBoolLit x) = pure e
  resolve h p (EBoolAnd x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EBoolAnd x' y')
  resolve h p e@ENatural = pure e
  resolve h p e@(ENaturalLit k) = pure e
  resolve h p (ENaturalIsZero x) = do
    x' <- resolve h p x
    pure (ENaturalIsZero x')
  resolve h p (EList x) = do
    x' <- resolve h p x
    pure (EList x')
  resolve h p (EListLit Nothing xs) = do
    xs' <- resolveList h p xs
    pure (EListLit Nothing xs')
  resolve h p (EListLit (Just x) xs) = do
    x' <- resolve h p x
    xs' <- resolveList h p xs
    pure (EListLit (Just x') xs')
  resolve h p (EListAppend x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EListAppend x' y')
  resolve h p (EEmbed (Raw (LocalFile x))) = resolveLocalFile h p x
  resolve h p (EEmbed (Raw (EnvVar x))) = MkIOEither (pure (Left (ErrorMessage "TODO not implemented")))
  resolve h p (EEmbed (Resolved x)) = MkIOEither (pure (Left (ErrorMessage "Already resolved")))

  resolveList :  (history : List FilePath)
              -> Maybe FilePath
              -> List (Expr ImportStatement)
              -> IOEither Error (List (Expr Void))
  resolveList h p [] = MkIOEither (pure (Right []))
  resolveList h p (x :: xs) =
    let rest = resolveList h p xs in
    do rest' <- rest
       x' <- resolve h p x
       MkIOEither (pure (Right (x' :: rest')))
