module Main

import Idrall.TestHelper

import Idrall.Error
import Idrall.IOEither
import Idrall.APIv1

import System.Directory
import Data.List
import Data.String

expectPass : List String
expectPass = ["AssertTrivial", "Bool", "Function", "Natural", "True", "NaturalIsZero", "NaturalLiteral", "Let", "FunctionTypeTermTerm", "FunctionApplication", "Equivalence", "FunctionDependentType1", "List", "ListLiteralOne", "ListLiteralEmpty", "ListHead", "OperatorListConcatenate", "Optional", "None", "SomeTrue", "Integer", "IntegerLiteral", "IntegerNegate", "UnionTypeType", "UnionTypeOne", "UnionTypeMixedKinds4", "UnionTypeMixedKinds3", "UnionTypeMixedKinds2", "UnionTypeMixedKinds1", "UnionTypeKind", "UnionTypeEmpty", "UnionConstructorField", "UnionConstructorEmptyField", "TypeAnnotation", "TypeAnnotationFunction", "TypeAnnotationSort", "Text", "TextLiteral", "TextLiteralWithInterpolation", "Double", "DoubleLiteral", "ListIndexed"]

asDirTree : DirTree String
asDirTree = MkDirTree "../../../dhall-lang/tests/type-inference/success/unit" [] expectPass

testGood : IO (Result)
testGood = runTestsCheck asDirTree

main : IO ()
main = do
  res <- runTestsOnly expectPass "../../../dhall-lang/tests/type-inference/success" roundTripCheck
  putStrLn $ ppResult res
