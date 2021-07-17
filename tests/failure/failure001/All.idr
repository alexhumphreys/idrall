module Main

import Idrall.TestHelper

import Idrall.Expr
import Idrall.Value
import Idrall.Error
import Idrall.IOEither
import Idrall.APIv1
import Idrall.Parser

import System
import System.Directory
import Data.List
import Data.String
import Data.String

main : IO ()
main = do
  res <- runTestFail "../../../dhall-lang/tests/type-inference/failure" roundTripSynth
  putStrLn $ ppResultFail res
