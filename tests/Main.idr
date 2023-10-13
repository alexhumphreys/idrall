module Main

import Data.Maybe
import Data.List
import Data.List1
import Data.String

import System
import System.Directory
import System.File
import System.Info
import System.Path

import Test.Golden

%default covering

allTests : TestPool
allTests = MkTestPool "dhall-lang tests" [] Default
  [ "idrall001"
  , "idrall002"
  , "idrall003"
  , "idrall004"
  , "idrall005"
  ]

failTests : TestPool
failTests = MkTestPool "dhall-lang expected fail tests" [] Default
  [ "failure001"
  ]

deriveTests : TestPool
deriveTests = MkTestPool "derive tests" [] Default
  [ "derive001"
  , "derive002"
  , "derive003"
  ]

examplesTests : TestPool
examplesTests = MkTestPool "examples tests" [] Default
  [ "example001"
  , "example002"
  , "inigo001"
  ]

main : IO ()
main = runner
  [ testPaths "idrall" allTests
  , testPaths "failure" failTests
  , testPaths "derive" deriveTests
  , testPaths "examples" examplesTests
  ] where

    testPaths : String -> TestPool -> TestPool
    testPaths dir = { testCases $= map ((dir ++ "/") ++) }
