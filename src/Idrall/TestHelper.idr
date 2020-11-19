module Idrall.TestHelper

import Idrall.Error
import Idrall.IOEither
import Idrall.API

import System.Directory
import Data.List
import Data.Strings

public export
dirName : String
dirName = "../../../dhall-lang/tests/type-inference/success/unit/"

public export
listDir : Directory -> List String -> IO (List String)
listDir d  ls = do
  dx <- dirEntry d
  case dx of
    Left  de => pure ls         --no more entries, return the list
    Right sn => listDir d (sn :: ls)

public export
stripSuffix : String -> String
stripSuffix x =
  let revX = reverse x
      listX = unpack revX
      rest = drop 7 listX
  in
  pack (reverse rest)

public export
onlyA : List String -> List String
onlyA xs = filter (isSuffixOf "A.dhall") xs

public export
resultIOEither : IOEither a b -> IO (Nat, Nat)
resultIOEither (MkIOEither x) =
  do x' <- x
     case x' of
          (Left l) => pure (Z, 1)
          (Right r) => pure (1, Z)

public export
testInferenceAB : String -> IOEither Error ()
testInferenceAB str =
  let dir = dirName
      aFile = dir ++ str ++ "A.dhall"
      bFile = dir ++ str ++ "B.dhall"
  in do
      a <- mapErr (fileErrorHandler aFile) $ MkIOEither (do readFile aFile)
      b <- mapErr (fileErrorHandler bFile) $ MkIOEither (do readFile bFile)
      roundTripCheck a b

public export
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
