module Main

import Idrall.TestHelper

import Idrall.Error
import Idrall.Value
import Idrall.IOEither
import Idrall.APIv1

import System.Directory
import Data.List
import Data.Strings

testImport : IOEither Error Value
testImport = do
  roundTripEval "/tmp/foo.dhall"

testImportFail : IOEither Error Value
testImportFail = do
  roundTripEval "/tmp/importFailA.dhall"

testImportEnv : IOEither Error Value
testImportEnv = do
  roundTripEval "env:IDRALL_TEST"

main : IO ()
main = do
  putStrLn !(showIOEither testImport)
  putStrLn !(showIOEither testImportFail)
  putStrLn !(showIOEither testImportEnv)
