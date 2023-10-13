module Main

import Idrall.API.V2
import Idrall.Pretty
import Text.PrettyPrint.Prettyprinter.Render.Terminal

import System

import Language.Reflection

%language ElabReflection

testPretty : ToDhall ty => ty -> IO ()
testPretty x = do
  putDoc $ pretty $ toDhall x

record NeedsTranslation where
  constructor MkNeedsTranslation
  ns : String
  name : String

dhallOptions : Options
dhallOptions = { fieldNameModifier := \case "ns" => "namespace"; fieldName => fieldName } defaultOptions

%runElab deriveFromDhall Record {options=dhallOptions} `{ NeedsTranslation }
%runElab deriveToDhall Record {options=dhallOptions} `{ NeedsTranslation }

main : IO ()
main = do
  testPretty $ MkNeedsTranslation "myNamespace" "myName"
  Right fromD <- liftIOEither $ 
    deriveFromDhallString {ty=NeedsTranslation} 
                          #" { namespace = "hi", name = "there" } "#
    | Left e => putStrLn (show e)
  if (fromD.ns /= "hi" || fromD.name /= "there")
     then putStrLn "from dhall failed"
     else pure ()

