module Test

import Idrall.Expr
import Idrall.Value
import Idrall.Error
import Idrall.Check
import Idrall.Parser
import Idrall.Resolve
import Idrall.IOEither
import Idrall.Path

trimString : Nat -> String -> String
trimString k str = pack (take k (unpack str))

eitherIO : Show a => Either a b -> IO (Either () b)
eitherIO (Left l) = do putStrLn (trimString 200 (show l)) -- TODO quite slow
                       pure (Left ())
eitherIO (Right r) = pure (Right r)

stringToExpr : String -> IO (Either () (Expr ImportStatement))
stringToExpr x = eitherIO (parseExpr x)

resolveExpr : Expr ImportStatement -> IO (Either () (Expr Void))
resolveExpr x = let xRes = resolve Nothing x in
  (case xRes of
        (MkIOEither x') => do x'' <- x'
                              eitherIO x'')

exprToValue : Expr Void -> IO (Either () Value)
exprToValue e = eitherIO (eval initEnv e)

checkExpr : Expr Void -> Value -> IO ()
checkExpr x y
  = do res <- eitherIO (check initCtx x y)
       case res of
            (Left l) => pure ()
            (Right r) => putStrLn ("SUCCESS")

dirName : String
dirName = "dhall-lang/tests/type-inference/success/unit/"

listDir : Directory -> List String -> IO (List String)
listDir d  ls = do
  dx <- dirEntry d
  case dx of
    Left  de => pure ls         --no more entries, return the list
    Right sn => listDir d (sn :: ls)

stripSuffix : String -> String
stripSuffix x =
  let revX = reverse x
      listX = unpack revX
      rest = drop 7 listX
  in
  pack (reverse rest)

onlyA : List String -> List String
onlyA xs = filter (isSuffixOf "A.dhall") xs

testAB' : String -> IO ()
testAB' str =
  let dir = "dhall-lang/tests/type-inference/success/unit/"
      aFile = dir ++ str ++ "A.dhall"
      bFile = dir ++ str ++ "B.dhall"
  in
  do
  putStrLn ("testing: " ++ str)
  Right a <- readFile aFile | Left x => putStrLn (show x)
  Right aExpr <- stringToExpr a | Left x => do putStrLn ("Parse error: " ++ aFile)
  Right b <- readFile bFile | Left x => putStrLn (show x)
  Right bExpr <- stringToExpr b | Left x => do putStrLn ("Parse error: " ++ bFile)
  Right aRes <- resolveExpr aExpr | Left x => do putStrLn ("Resolve error: " ++ aFile)
  Right bRes <- resolveExpr bExpr | Left x => do putStrLn ("Resolve error: " ++ bFile)
  Right bVal <- exprToValue bRes | Left x => putStrLn ("eval error: " ++ bFile)
  checkExpr aRes bVal

testAB : List String -> IO ()
testAB [] = do pure ()
testAB (x :: xs) = do
  testAB' x
  testAB xs

testAll : IO ()
testAll = do
  putStrLn ("Listing directory " ++ dirName)
  dh <- dirOpen dirName
  case dh of
    Left er => putStrLn "directory not found"
    Right d => do
      entries <- listDir d []
      testAB (map stripSuffix (onlyA (sort entries)))
      putStrLn "done"

expectPass : List String
expectPass = ["AssertTrivial", "Bool", "Function", "Natural", "True", "NaturalIsZero", "NaturalLiteral", "Let", "FunctionTypeTermTerm", "FunctionApplication", "Equivalence", "FunctionDependentType1", "List", "ListLiteralOne", "ListLiteralEmpty", "OperatorListConcatenate"]

testGood : IO ()
testGood
  = do testAB expectPass
       putStrLn "done"

testImport : IO ()
testImport = do
  Right expr <- stringToExpr "/tmp/bar.dhall" | Left x => do putStrLn ("Parse error")
  Right aRes <- resolveExpr expr | Left x => do putStrLn ("Resolve error: " ++ (show expr))
  putStrLn (show aRes)
