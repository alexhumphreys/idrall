module Main

import Idrall.API.V2
import Idrall.Pretty
import Text.PrettyPrint.Prettyprinter.Render.Terminal

testPretty : ToDhall ty => ty -> IO ()
testPretty x = do
  putDoc $ pretty $ toDhall x

record Foo where
  constructor MkFoo
  someNat : Nat

ToDhall Foo where
  toDhallType =
    ERecord EmptyFC $ fromList [ (MkFieldName "someNat", ENatural EmptyFC) ]
  toDhall foo = ERecordLit EmptyFC $ fromList [ (MkFieldName "someNat", (toDhall $ someNat foo)) ]

data ExADTTest
  = ADouble Double
  | Bar

ToDhall ExADTTest where
  toDhallType =
    EUnion EmptyFC $
      fromList [ (MkFieldName "ADouble", Just $ EDouble EmptyFC)
               , (MkFieldName "Bar", Nothing)
               ]
  toDhall (ADouble x) =
    let field = EField EmptyFC (toDhallType {ty=ExADTTest}) (MkFieldName "ADouble")
    in EApp EmptyFC field (toDhall x)
  toDhall Bar =
    EField EmptyFC (toDhallType {ty=ExADTTest}) (MkFieldName "Bar")

main : IO ()
main = do
  testPretty $ the (List Nat) [1,2,3]
  testPretty $ the (Integer) 10
  testPretty $ Just "foo"
  testPretty $ the (Maybe Bool) Nothing
  testPretty $ True
  testPretty $ 2.4
  testPretty $ MkFoo 20
  testPretty $ ADouble 30.0
  testPretty $ Bar
