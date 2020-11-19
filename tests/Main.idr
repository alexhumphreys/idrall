module Main

import Data.Maybe
import Data.List
import Data.List1
import Data.Strings

import System
import System.Directory
import System.File
import System.Info
import System.Path

import Test.Golden

%default covering

allTests : TestPool
allTests = MkTestPool []
  [ "idrall001"
  , "idrall002"
  , "idrall003"
  ]

main : IO ()
main = runner
  [ testPaths "idrall" allTests
  ] where

    testPaths : String -> TestPool -> TestPool
    testPaths dir = record { testCases $= map ((dir ++ "/") ++) }
