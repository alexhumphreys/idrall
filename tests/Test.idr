module Test

import Idrall.Expr
import Idrall.Check
import Idrall.Parser

eitherIO : Show a => Either a b -> IO (Either () b)
eitherIO (Left l) = do putStrLn (show l) -- TODO silence parse errors
                       pure (Left ())
eitherIO (Right r) = pure (Right r)

stringToExpr : String -> IO (Either () Expr)
stringToExpr x = eitherIO (parseExpr x)

exprToValue : Expr -> IO (Either () Value)
exprToValue e = eitherIO (eval initEnv e)

checkExpr : Expr -> Value -> IO ()
checkExpr x y
  = do res <- eitherIO (check initCtx x y)
       case res of
            (Left l) => pure ()
            (Right r) => putStrLn ("Success")

testBool : IO ()
testBool = do Right a <- readFile "dhall-lang/tests/type-inference/success/unit/BoolA.dhall"
              Right aExpr <- stringToExpr a
              Right b <- readFile "dhall-lang/tests/type-inference/success/unit/BoolB.dhall"
              Right bExpr <- stringToExpr b
              Right bVal <- exprToValue bExpr
              checkExpr aExpr bVal

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

test : IO ()
test = do
  putStrLn ("Listing directory " ++ dirName)
  dh <- dirOpen dirName
  case dh of
    Left er => putStrLn "directory not found"
    Right d => do
      entries <- listDir d []
      putStrLn (show (map stripSuffix (onlyA (sort entries))))
      putStrLn "done"

testAB : String -> IO ()
testAB str =
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
  Right bVal <- exprToValue bExpr | Left x => putStrLn ("eval error: " ++ bFile)
  checkExpr aExpr bVal

testAB' : List String -> IO ()
testAB' [] = putStrLn "Done"
testAB' (x :: xs) = do
  testAB x
  testAB' xs

testAll : IO ()
testAll = do
  putStrLn ("Listing directory " ++ dirName)
  dh <- dirOpen dirName
  case dh of
    Left er => putStrLn "directory not found"
    Right d => do
      entries <- listDir d []
      -- putStrLn (show (map stripSuffix (onlyA (sort entries))))
      testAB' (map stripSuffix (onlyA (sort entries)))
      putStrLn "done"
