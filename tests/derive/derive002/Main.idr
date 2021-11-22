module Main

import Idrall.API.V2
import Idrall.Pretty
import Text.PrettyPrint.Prettyprinter.Render.Terminal

testPretty : ToDhall ty => ty -> IO ()
testPretty x =
  let dhall = toDhall x
  in case dhall of
          (Left y) => do
            putStrLn $ show y
          (Right y) => do
            putDoc $ pretty y

main : IO ()
main = do
  testPretty $ the (List Nat) [1,2,3]
  testPretty $ the (Integer) 10
  testPretty $ Just "foo"
  testPretty $ the (Maybe Bool) Nothing
  testPretty $ True
  testPretty $ 2.4
