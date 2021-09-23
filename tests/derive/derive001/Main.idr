module Main

import Idrall.API.V2

import Language.Reflection
%language ElabReflection

record ExRec2 where
  constructor MkExRec2
  mn : Maybe Nat
  n : Nat
  i : Integer
  b : Bool
  d : Double
  lb : List Bool
  st : String
  mst : Maybe String
  mst2 : Maybe String
%runElab (deriveFromDhall Record `{ ExRec2 })

Show ExRec2 where
  show (MkExRec2 mn n i b d lb st mst mst2) =
    "(MkExample3 \{show mn} \{show n} \{show i} \{show b} \{show d} \{show lb} \{show st} \{show mst} \{show mst2})"

data ExADT1 = A Nat | B
%runElab (deriveFromDhall ADT `{ ExADT1 })

Show ExADT1 where
  show (A x) = "A \{show x}"
  show B = "B"

data ExADT2
  = Foo
  | Bar Bool
  | Baz (Maybe Bool)

Show ExADT2 where
  show Foo = "Foo"
  show (Bar x) = "(Bar \{show x})"
  show (Baz x) = "(Baz \{show x})"
%runElab (deriveFromDhall ADT `{ ExADT2 })

printRes : Show a => Either Error a -> IO String
printRes (Left x) = fancyError x
printRes (Right x) = pure $ show x

runTest : Show ty => FromDhall ty => String -> IO ()
runTest {ty} str = do
  res <- liftIOEither $ deriveFromDhallString {ty=ty} str
  putStrLn $ !(printRes res)

main : IO ()
main = do
  runTest {ty=ExADT1} "< A : Natural | B >.A 0"
  runTest {ty=ExADT1} "< A : Natural | B >.B"
  runTest {ty=ExADT1} "./fail-exadt1.dhall"
  runTest {ty=ExADT2} "< Foo | Bar : Bool | Baz : Optional Bool >.Foo"
  runTest {ty=ExADT2} "< Foo | Bar : Bool | Baz : Optional Bool >.Bar True"
  runTest {ty=ExADT2} "< Foo | Bar : Bool | Baz : Optional Bool >.Baz (Some True)"
  runTest {ty=ExADT2} "< Foo | Bar : Bool | Baz : Optional Bool >.hello False"
  runTest {ty=ExRec2} "{ mn = Some 1, n = 0, i = -1, b = True, d = 2.0, lb = [True,False], st = \"foo\", mst = Some \"yeah\", mst2 = Some \"nah\" }"
  runTest {ty=ExRec2} "./fail-exadt2.dhall"
  runTest {ty=ExRec2} "./fail-exrec1.dhall"
