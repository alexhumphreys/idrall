module Idrall.Resolve

import Idrall.Error
import Idrall.Expr
import Idrall.IOEither
import Idrall.Parser
import Idrall.Path

import System.File

parseErrorHandler : String -> Error
parseErrorHandler x = ErrorMessage (x)

fileErrorHandler : String -> FileError -> Error
fileErrorHandler x y = ReadFileError (show y ++ " " ++ x)

readFile' : String -> IOEither Error String
readFile' x =
  let contents = MkIOEither (readFile x) in
      mapErr (fileErrorHandler x) contents

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
      expr <- mapErr parseErrorHandler (liftEither (parseExpr str))
      resolve (normaliseFilePath p :: h) (Just p) (fst expr)

  export
  covering
  resolve : (history : List FilePath) -> Maybe FilePath -> Expr ImportStatement -> IOEither Error (Expr Void)
  resolve h p (EVar x) = pure (EVar x)
  resolve h p (EConst x) = pure (EConst x)
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
  resolve h p EBool = pure EBool
  resolve h p (EBoolLit x) = pure (EBoolLit x)
  resolve h p (EBoolAnd x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EBoolAnd x' y')
  resolve h p EInteger = pure EInteger
  resolve h p (EIntegerLit k) = pure (EIntegerLit k)
  resolve h p ENatural = pure ENatural
  resolve h p (ENaturalLit k) = pure (ENaturalLit k)
  resolve h p (ENaturalIsZero x) = do
    x' <- resolve h p x
    pure (ENaturalIsZero x')
  resolve h p EDouble = pure EDouble
  resolve h p (EDoubleLit k) = pure (EDoubleLit k)
  resolve h p (EIntegerNegate x) = do
    x' <- resolve h p x
    pure (EIntegerNegate x')
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
  resolve h p (EListHead x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EListHead x' y')
  resolve h p (EListFold) = pure EListFold
  resolve h p EText = pure EText
  resolve h p (ETextLit (MkChunks xs x)) = do
    xs' <- resolveChunks h p xs
    pure (ETextLit (MkChunks xs' x))
  resolve h p (EOptional x) = do
    x' <- resolve h p x
    pure (EOptional x')
  resolve h p (ENone x) = do
    x' <- resolve h p x
    pure (ENone x')
  resolve h p (ESome x) = do
    x' <- resolve h p x
    pure (ESome x')
  resolve h p (ERecord x) =
    let kv = toList x in do
      kv' <- resolveRecord h p kv
      pure (ERecord (fromList kv'))
  resolve h p (ERecordLit x) =
    let kv = toList x in do
      kv' <- resolveRecord h p kv
      pure (ERecordLit (fromList kv'))
  resolve h p (ECombine x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (ECombine x' y')
  resolve h p (ECombineTypes x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (ECombineTypes x' y')
  resolve h p (EUnion x) =
    let kv = toList x in do
      kv' <- resolveUnion h p kv
      pure (EUnion (fromList kv'))
  resolve h p (EField x y) = do
    pure (EField !(resolve h p x) y)
  resolve h p (EEmbed (Raw (LocalFile x))) = resolveLocalFile h p x
  resolve h p (EEmbed (Raw (EnvVar x))) = MkIOEither (pure (Left (ErrorMessage "TODO not implemented")))
  resolve h p (EEmbed (Resolved x)) = MkIOEither (pure (Left (ErrorMessage "Already resolved")))

  resolveRecord :  (history : List FilePath)
               -> Maybe FilePath
               -> List (FieldName, Expr ImportStatement)
               -> IOEither Error (List (FieldName, Expr Void))
  resolveRecord h p [] =  MkIOEither (pure (Right []))
  resolveRecord h p ((k, v) :: xs) = do
    rest <- resolveRecord h p xs
    MkIOEither (pure (Right ((k, !(resolve h p v)) :: rest)))

  resolveUnion :  (history : List FilePath) -- TODO try use traverse instead?
               -> Maybe FilePath
               -> List (FieldName, Maybe (Expr ImportStatement))
               -> IOEither Error (List (FieldName, Maybe (Expr Void)))
  resolveUnion h p [] = MkIOEither (pure (Right []))
  resolveUnion h p ((k,v) :: xs) = do
    rest <- resolveUnion h p xs
    case v of
         Nothing => MkIOEither (pure (Right ((k, Nothing) :: rest)))
         (Just x) => MkIOEither (pure (Right ((k, Just (!(resolve h p x))) :: rest)))

  resolveList :  (history : List FilePath)
              -> Maybe FilePath
              -> List (Expr ImportStatement)
              -> IOEither Error (List (Expr Void))
  resolveList h p [] = MkIOEither (pure (Right []))
  resolveList h p (x :: xs) =
    do rest <- resolveList h p xs
       x' <- resolve h p x
       MkIOEither (pure (Right (x' :: rest)))

  resolveChunks :  (history : List FilePath)
                -> Maybe FilePath
                -> List (String, Expr ImportStatement)
                -> IOEither Error (List (String, Expr Void))
  resolveChunks h p [] = MkIOEither $ pure (Right [])
  resolveChunks h p ((a, x) :: xs) = do
    rest <- resolveChunks h p xs
    x' <- resolve h p x
    MkIOEither (pure (Right ((a, x') :: rest)))
