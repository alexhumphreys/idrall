module Main

import Idrall.TestHelper

import Idrall.Error
import Idrall.IOEither
import Idrall.APIv1

import System.Directory
import Data.List
import Data.String

expectPass : List String
expectPass = map (\x => "\{x}A.dhall") ["AssertTrivial", "Bool", "Function", "Natural", "True", "NaturalIsZero", "NaturalLiteral", "Let", "FunctionTypeTermTerm", "FunctionApplication", "Equivalence", "FunctionDependentType1", "List", "ListLiteralOne", "ListLiteralEmpty", "ListHead", "OperatorListConcatenate", "Optional", "None", "SomeTrue", "Integer", "IntegerLiteral", "IntegerNegate", "UnionTypeType", "UnionTypeOne", "UnionTypeMixedKinds4", "UnionTypeMixedKinds3", "UnionTypeMixedKinds2", "UnionTypeMixedKinds1", "UnionTypeKind", "UnionTypeEmpty", "UnionConstructorField", "UnionConstructorEmptyField", "TypeAnnotation", "TypeAnnotationFunction", "TypeAnnotationSort", "Text", "TextLiteral", "TextLiteralWithInterpolation", "Double", "DoubleLiteral", "ListIndexed"]

main : IO ()
main = do
  res <- runTestsOnly expectPass "../../../dhall-lang/tests/type-inference/success" roundTripCheck
  putStrLn $ ppResult res
