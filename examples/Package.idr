module Main

import Idrall.API.V2

import Language.Reflection
%language ElabReflection

record Package where
  constructor MkPackage
  package : String
  sourceDir : Maybe String
  depends : Maybe (List String)
  modules : List String
%runElab (deriveFromDhall Record `{{ Package }})

Show Package where
  show (MkPackage package sourceDir depends modules) =
    "MkPackage \{show package} \{show sourceDir} \{show depends} \{show modules}"

main : IO ()
main = do
  package <- liftIOEither $ deriveFromDhallString {ty=Package} "./package.dhall"
  putStrLn $ show package
