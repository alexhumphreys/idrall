module ForbiddenNames

import Idrall.API.V2

import Language.Reflection
%language ElabReflection

record ForbiddenNames where
  constructor MkForbiddenNames
  ns : String
  rc : String

dhallOptions : Options
dhallOptions =
  { fieldNameModifier :=
    \case "ns" => "namespace"; "rc" => "record"; fieldName => fieldName } defaultOptions

%runElab deriveFromDhall Record {options=dhallOptions} `{ ForbiddenNames }
%runElab deriveToDhall Record {options=dhallOptions} `{ ForbiddenNames }

main : IO ()
main = do
  Right names <- liftIOEither $ deriveFromDhallString {ty=ForbiddenNames} "./forbidden-names.dhall"
    | Left e => putStrLn $ !(fancyError e)
  putStrLn $ "namespace: " ++ names.ns
  putStrLn $ "record: " ++ names.rc
