module Main

import Idrall.API.V2
import Idrall.Pretty
import Text.PrettyPrint.Prettyprinter.Render.Terminal

import Language.Reflection

%language ElabReflection

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

record Foo2 where
  constructor MkFoo2
  someNat, someNat1 : Nat
  someStr : String
  someList : List Double
  someOpBool : Maybe Bool

%runElab (deriveToDhall Record `{ Foo2 })

data ExADTTest2
  = ADouble2 Double
  | Bar2
  | Baz Nat

%runElab (deriveToDhall ADT `{ ExADTTest2 })

main : IO ()
main = do
  testPretty $ the (List Nat) [1,2,3]
  testPretty $ the (List Bool) []
  testPretty $ the (Integer) 10
  testPretty $ Just "foo"
  testPretty $ the (Maybe Bool) Nothing
  testPretty $ True
  testPretty $ 2.4
  testPretty $ MkFoo 20
  testPretty $ ADouble 30.0
  testPretty $ Bar
  testPretty $ MkFoo2 2 3 "mkfoo" [1.2, 3.4] $ Just True
  testPretty $ ADouble2 40.0
  testPretty $ Bar2
  testPretty $ Baz 1
