module Main

import Idrall.TestHelper

import Idrall.Error
import Idrall.Value
import Idrall.IOEither
import Idrall.APIv1

import System.Directory
import Data.List
import Data.String

testImport : IOEither Error Value
testImport = do
  roundTripEval "/tmp/foo.dhall"

testImportFail : IOEither Error Value
testImportFail = do
  roundTripEval "/tmp/importFailA.dhall"

testImportEnv : IOEither Error Value
testImportEnv = do
  roundTripEval "env:IDRALL_TEST"

testImportEnvAsText : IOEither Error Value
testImportEnvAsText = do
  roundTripEval "env:IDRALL_TEST as Text"

main : IO ()
main = do
  putStrLn !(showIOEither testImport)
  putStrLn !(showIOEither testImportFail)
  putStrLn !(showIOEither testImportEnv)
  putStrLn !(showIOEither testImportEnvAsText)
