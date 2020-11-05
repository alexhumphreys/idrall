module Test2

import Idrall.Expr
import Idrall.Value
import Idrall.Error
import Idrall.Check
import Idrall.Parser
import Idrall.Resolve
import Idrall.IOEither
import Idrall.Path

%hide Language.Reflection.Elab.Tactics.check

-- Directory Stuff
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

-- Test Stuff

handleError : String -> Error
handleError x = ErrorMessage x

exprFromString : String -> IOEither Error (Expr Void)
exprFromString x = do
  x' <- mapErr (handleError) (liftEither (parseExpr x))
  resolve [] Nothing x'

roundTripEval : String -> IOEither Error Value
roundTripEval x = do
  x' <- exprFromString x
  liftEither (eval initEnv x')

roundTripSynth : String -> IOEither Error Value
roundTripSynth x = do
  x' <- exprFromString x
  liftEither (synth initCtx x')

roundTripCheck : String -> String -> IOEither Error ()
roundTripCheck x y = do
  x' <- exprFromString x
  y' <- roundTripEval y
  liftEither (check initCtx x' y')

showIOEither : Show a => Show b => IOEither a b -> IO String
showIOEither (MkIOEither x) =
  do x' <- x
     case x' of
          (Left l) => pure $ "Error: " ++ show l
          (Right r) => pure $ "Success: " ++ show r

resultIOEither : IOEither a b -> IO (Nat, Nat)
resultIOEither (MkIOEither x) =
  do x' <- x
     case x' of
          (Left l) => pure (Z, 1)
          (Right r) => pure (1, Z)

fileErrorHandler : String -> FileError -> Error
fileErrorHandler x y = ErrorMessage x -- ?fileErrorHandler_rhs

testInferenceAB : String -> IOEither Error ()
testInferenceAB str =
  let dir = "dhall-lang/tests/type-inference/success/unit/"
      aFile = dir ++ str ++ "A.dhall"
      bFile = dir ++ str ++ "B.dhall"
  in do
      a <- mapErr (fileErrorHandler aFile) $ MkIOEither (do readFile aFile)
      b <- mapErr (fileErrorHandler bFile) $ MkIOEither (do readFile bFile)
      roundTripCheck a b

testAB : (pass : Nat) -> (fail : Nat) -> List String -> IO ()
testAB p f [] = do
  putStrLn "DONE"
  putStrLn ("Passed: " ++ show p)
  putStrLn ("Failed: " ++ show f)
testAB p f (x :: xs) =
  let foo = testInferenceAB x in do
    putStrLn ("testing: " ++ x)
    x' <- showIOEither foo -- TODO toggle with debug somehow
    putStrLn x'
    (p', f') <- resultIOEither foo
    testAB (p+p') (f+f') xs

testAll : IO ()
testAll = do
  putStrLn ("Listing directory " ++ dirName)
  dh <- dirOpen dirName
  case dh of
    Left er => putStrLn "directory not found"
    Right d => do
      entries <- listDir d []
      testAB Z Z (map stripSuffix (onlyA (sort entries)))

expectPass : List String
expectPass = ["AssertTrivial", "Bool", "Function", "Natural", "True", "NaturalIsZero", "NaturalLiteral", "Let", "FunctionTypeTermTerm", "FunctionApplication", "Equivalence", "FunctionDependentType1", "List", "ListLiteralOne", "ListLiteralEmpty", "ListHead", "OperatorListConcatenate", "Optional", "None", "SomeTrue", "Integer", "IntegerLiteral", "IntegerNegate", "UnionTypeType", "UnionTypeOne", "UnionTypeMixedKinds4", "UnionTypeMixedKinds3", "UnionTypeMixedKinds2", "UnionTypeMixedKinds1", "UnionTypeKind", "UnionTypeEmpty", "UnionConstructorField", "UnionConstructorEmptyField", "TypeAnnotation", "TypeAnnotationFunction", "TypeAnnotationSort", "Text", "TextLiteral", "TextLiteralWithInterpolation"]

testGood : IO ()
testGood = testAB Z Z expectPass

doStuff : Show a => Show b => (String -> IOEither a b) -> String -> IO ()
doStuff f x =
  putStrLn !(showIOEither (f x))
