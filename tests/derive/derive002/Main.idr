module Main

import Idrall.API.V2

import Language.Reflection
%language ElabReflection

data Foo1 = A Nat | B
%runElab (deriveFromDhall ADT `{ Foo1 })

Show Foo1 where
  show (A x) = "A \{show x}"
  show B = "B"

printRes : Show a => Either Error a -> IO String
printRes (Left x) = fancyError x
printRes (Right x) = pure $ show x

runTest : Show ty => FromDhall ty => String -> IO ()
runTest {ty} str = do
  res <- liftIOEither $ deriveFromDhallString {ty=ty} str
  putStrLn $ !(printRes res)

main : IO ()
main = do
  runTest {ty=Foo1} "< A : Natural | B >.A 0"
  runTest {ty=Foo1} "< A : Natural | B >.B"
