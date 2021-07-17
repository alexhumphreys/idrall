module Main

import Idrall.TestHelper

import Idrall.Error
import Idrall.IOEither
import Idrall.APIv1

import System.Directory
import Data.List
import Data.String

expectPass : List String
expectPass = ["toMapEmptyNormalizeAnnotationA.dhall"]

main : IO ()
main = do
  res <- runTestsOnly expectPass "../../../dhall-lang/tests/type-inference/success/simple" roundTripCheck
  putStrLn $ ppResult res
