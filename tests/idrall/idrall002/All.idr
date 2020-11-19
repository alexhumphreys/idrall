module Main

import Idrall.TestHelper

import Idrall.Error
import Idrall.IOEither
import Idrall.API

import System.Directory
import Data.List
import Data.Strings

testAll : IO ()
testAll = do
  putStrLn ("Listing directory " ++ dirName)
  dh <- openDir dirName
  case dh of
    Left er => putStrLn "directory not found"
    Right d => do
      entries <- listDir d []
      testAB Z Z (map stripSuffix (onlyA (sort entries)))

main : IO ()
main = do testAll
