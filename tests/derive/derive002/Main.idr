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

record Foo where
  constructor MkFoo
  someNat : Nat

ToDhall Foo where
  toDhallType = Right $
    ERecord EmptyFC $ fromList [ (MkFieldName "n", ENatural EmptyFC) ]
  toDhall foo = Right $ ERecordLit EmptyFC $ fromList [ (MkFieldName "n", !(toDhall $ someNat foo)) ]

main : IO ()
main = do
  testPretty $ the (List Nat) [1,2,3]
  testPretty $ the (Integer) 10
  testPretty $ Just "foo"
  testPretty $ the (Maybe Bool) Nothing
  testPretty $ True
  testPretty $ 2.4
  testPretty $ MkFoo 20
