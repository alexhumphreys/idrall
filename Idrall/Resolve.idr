module Idrall.Resolve

import Idrall.Error
import Idrall.Expr
import Idrall.IOEither
import Idrall.Parser
import Idrall.ParserNew
import Idrall.Path

import System
import System.File

data WhichParser = OldParser | NewParser

useParser : WhichParser
useParser = OldParser
-- useParser = NewParser

parseFunction : WhichParser -> Maybe String -> String -> Either String (Expr ImportStatement, Int)
parseFunction OldParser x = Idrall.Parser.parseExpr
parseFunction NewParser x = Idrall.ParserNew.parseExprNew {od = x}

parseWith : Maybe String -> String -> Either String (Expr ImportStatement, Int)
parseWith x = parseFunction useParser x

parseErrorHandler : FC -> String -> Error
parseErrorHandler fc x = ParseError fc x

fileErrorHandler : FC -> String -> FileError -> Error
fileErrorHandler fc x y = ReadFileError fc (show y ++ " " ++ x)

readEnvVar : FC -> String -> IOEither Error String
readEnvVar fc x =
  MkIOEither $ do
    Just x' <- getEnv x | Nothing => pure $ Left $ EnvVarError fc $ "Env var \{x} not found"
    pure $ pure x'

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

alreadyImported : FC -> List FilePath -> FilePath -> Either Error () -- TODO check is correct
alreadyImported fc xs x = case elem x xs of
                            False => pure ()
                            True => Left (CyclicImportError fc ((show x) ++ " in " ++ (show xs)))

mutual
  resolveEnvVar : FC -> (history : List FilePath) -> Maybe FilePath -> String -> IOEither Error (Expr Void)
  resolveEnvVar fc h p x = do
    str <- readEnvVar fc x
    expr <- mapErr (parseErrorHandler fc) (liftEither (parseWith Nothing str))
    resolve h p (fst expr)

  resolveLocalFile : FC -> (history : List FilePath) -> (current : Maybe FilePath) -> (next : FilePath) -> IOEither Error (Expr Void)
  resolveLocalFile fc h current next =
    let combinedFilePaths = combinePaths current next in
        go combinedFilePaths
    where
    readFile' : String -> IOEither Error String
    readFile' x =
      let contents = MkIOEither (readFile x) in
          mapErr (fileErrorHandler fc x) contents
    go : FilePath -> IOEither Error (Expr Void)
    go p = do
      liftEither (alreadyImported fc h (normaliseFilePath p))
      let fp = canonicalFilePath p
      str <- readFile' fp
      expr <- mapErr (parseErrorHandler fc) (liftEither (parseWith (Just fp) str))
      resolve (normaliseFilePath p :: h) (Just p) (fst expr)

  export
  covering
  resolve : (history : List FilePath)
          -> Maybe FilePath
          -> Expr ImportStatement
          -> IOEither Error (Expr Void)
  resolve h p (EVar fc x i) = pure (EVar fc x i)
  resolve h p (EConst fc x) = pure (EConst fc x)
  resolve h p (EPi fc x y z) = do
    y' <- resolve h p y
    z' <- resolve h p z
    pure (EPi fc x y' z')
  resolve h p (ELam fc x y z) = do
    y' <- resolve h p y
    z' <- resolve h p z
    pure (ELam fc x y' z')
  resolve h p (EApp fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EApp fc x' y')
  resolve h p (ELet fc x Nothing z w) = do
    z' <- resolve h p z
    w' <- resolve h p w
    pure (ELet fc x Nothing z' w')
  resolve h p (ELet fc x (Just y) z w) = do
    y' <- resolve h p y
    z' <- resolve h p z
    w' <- resolve h p w
    pure (ELet fc x (Just y') z' w')
  resolve h p (EAnnot fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EAnnot fc x' y')
  resolve h p (EEquivalent fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EEquivalent fc x' y')
  resolve h p (EAssert fc x) = do
    x' <- resolve h p x
    pure (EAssert fc x')
  resolve h p (EBool fc) = pure $ EBool fc
  resolve h p (EBoolLit fc x) = pure (EBoolLit fc x)
  resolve h p (EBoolAnd fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EBoolAnd fc x' y')
  resolve h p (EBoolOr fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EBoolOr fc x' y')
  resolve h p (EBoolEQ fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EBoolEQ fc x' y')
  resolve h p (EBoolNE fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EBoolNE fc x' y')
  resolve h p (EBoolIf fc x y z) = do
    x' <- resolve h p x
    y' <- resolve h p y
    z' <- resolve h p z
    pure (EBoolIf fc x' y' z')
  resolve h p (ENatural fc) = pure $ ENatural fc
  resolve h p (ENaturalLit fc k) = pure $ ENaturalLit fc k
  resolve h p (ENaturalBuild fc) = pure $ ENaturalBuild fc
  resolve h p (ENaturalFold fc) = pure $ ENaturalFold fc
  resolve h p (ENaturalIsZero fc) = pure $ ENaturalIsZero fc
  resolve h p (ENaturalEven fc) = pure $ ENaturalEven fc
  resolve h p (ENaturalOdd fc) = pure $ ENaturalOdd fc
  resolve h p (ENaturalSubtract fc) = pure $ ENaturalSubtract fc
  resolve h p (ENaturalToInteger fc) = pure $ ENaturalToInteger fc
  resolve h p (ENaturalShow fc) = pure $ ENaturalShow fc
  resolve h p (ENaturalPlus fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (ENaturalPlus fc x' y')
  resolve h p (ENaturalTimes fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (ENaturalTimes fc x' y')
  resolve h p (EInteger fc) = pure $ EInteger fc
  resolve h p (EIntegerLit fc k) = pure $ EIntegerLit fc k
  resolve h p (EIntegerShow fc) = pure $ EIntegerShow fc
  resolve h p (EIntegerClamp fc) = pure $ EIntegerClamp fc
  resolve h p (EIntegerNegate fc) = pure $ EIntegerNegate fc
  resolve h p (EIntegerToDouble fc) = pure $ EIntegerToDouble fc
  resolve h p (EDouble fc) = pure $ EDouble fc
  resolve h p (EDoubleLit fc k) = pure $ EDoubleLit fc k
  resolve h p (EDoubleShow fc) = pure $ EDoubleShow fc
  resolve h p (EList fc) = pure $ EList fc
  resolve h p (EListLit fc Nothing xs) = do
    xs' <- resolveList h p xs
    pure (EListLit fc Nothing xs')
  resolve h p (EListLit fc (Just x) xs) = do
    x' <- resolve h p x
    xs' <- resolveList h p xs
    pure (EListLit fc (Just x') xs')
  resolve h p (EListAppend fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EListAppend fc x' y')
  resolve h p (EListBuild fc) = pure $ EListBuild fc
  resolve h p (EListFold fc) = pure $ EListFold fc
  resolve h p (EListLength fc) = pure $ EListLength fc
  resolve h p (EListHead fc) = pure $ EListHead fc
  resolve h p (EListLast fc) = pure $ EListLast fc
  resolve h p (EListIndexed fc) = pure $ EListIndexed fc
  resolve h p (EListReverse fc) = pure $ EListReverse fc
  resolve h p (EText fc) = pure $ EText fc
  resolve h p (ETextLit fc (MkChunks xs x)) = do
    xs' <- resolveChunks h p xs
    pure (ETextLit fc (MkChunks xs' x))
  resolve h p (ETextAppend fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (ETextAppend fc x' y')
  resolve h p (ETextShow fc) = pure $ ETextShow fc
  resolve h p (ETextReplace fc) = pure $ ETextReplace fc
  resolve h p (EOptional fc) = pure $ EOptional fc
  resolve h p (ENone fc) = pure $ ENone fc
  resolve h p (ESome fc x) = do
    x' <- resolve h p x
    pure (ESome fc x')
  resolve h p (ERecord fc x) =
    let kv = toList x in do
      kv' <- resolveRecord h p kv
      pure (ERecord fc (fromList kv'))
  resolve h p (ERecordLit fc x) =
    let kv = toList x in do
      kv' <- resolveRecord h p kv
      pure (ERecordLit fc (fromList kv'))
  resolve h p (ECombine fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (ECombine fc x' y')
  resolve h p (ECombineTypes fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (ECombineTypes fc x' y')
  resolve h p (EPrefer fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EPrefer fc x' y')
  resolve h p (ERecordCompletion fc x y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (ERecordCompletion fc x' y')
  resolve h p (EMerge fc x y Nothing) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EMerge fc x' y' Nothing)
  resolve h p (EMerge fc x y (Just z)) = do
    x' <- resolve h p x
    y' <- resolve h p y
    z' <- resolve h p z
    pure (EMerge fc x' y' (Just z'))
  resolve h p (EUnion fc x) =
    let kv = toList x in do
      kv' <- resolveUnion h p kv
      pure (EUnion fc (fromList kv'))
  resolve h p (EToMap fc x Nothing) = do
    x' <- resolve h p x
    pure (EToMap fc x' Nothing)
  resolve h p (EToMap fc x (Just y)) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EToMap fc x' (Just y'))
  resolve h p (EField fc x y) = do
    pure (EField fc !(resolve h p x) y)
  resolve h p (EProject fc x (Left y)) = do
    x' <- resolve h p x
    pure (EProject fc x' (Left y))
  resolve h p (EProject fc x (Right y)) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EProject fc x' (Right y'))
  resolve h p (EWith fc x ks y) = do
    x' <- resolve h p x
    y' <- resolve h p y
    pure (EWith fc x' ks y')
  resolve h p (EImportAlt fc x y) =
    case resolve h p x of
         (MkIOEither x') => MkIOEither $ do
           case !x' of
                (Right x'') => pure $ Right x''
                (Left w) => case resolve h p y of
                                 (MkIOEither y'') => y''
  resolve h p (EEmbed fc (Raw (LocalFile x))) = resolveLocalFile fc h p x
  resolve h p (EEmbed fc (Raw (EnvVar x))) = resolveEnvVar fc h p x
  resolve h p (EEmbed fc (Raw (Http x))) = MkIOEither (pure (Left (ErrorMessage fc "TODO http imports not implemented")))
  resolve h p (EEmbed fc (Raw Missing)) = MkIOEither (pure (Left (ErrorMessage fc "No valid imports")))
  resolve h p (EEmbed fc (Text a)) = MkIOEither (pure (Left (ErrorMessage fc "TODO as Text not implemented")))
  resolve h p (EEmbed fc (Location a)) = MkIOEither (pure (Left (ErrorMessage fc "TODO as Location not implemented")))
  resolve h p (EEmbed fc (Resolved x)) = MkIOEither (pure (Left (ErrorMessage fc "Already resolved")))

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
