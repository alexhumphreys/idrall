module Main

import Idrall.TestHelper

import Idrall.Error
import Idrall.IOEither
import Idrall.APIv1

import System
import System.Directory
import Data.List
import Data.String
import Data.String

main : IO ()
main = do
  res <- runTests "../../../dhall-lang/tests/normalization/success" roundTripConv
  putStrLn $ ppResult res
