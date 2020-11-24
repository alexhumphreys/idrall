module Main

import Idrall.TestHelper

import Idrall.Error
import Idrall.IOEither
import Idrall.API

import System.Directory
import Data.List
import Data.Strings

expectPass : List String
expectPass = ["AssertTrivial", "Bool", "Function", "Natural", "True", "NaturalIsZero", "NaturalLiteral", "Let", "FunctionTypeTermTerm", "FunctionApplication", "Equivalence", "FunctionDependentType1", "List", "ListLiteralOne", "ListLiteralEmpty", "ListHead", "OperatorListConcatenate", "Optional", "None", "SomeTrue", "Integer", "IntegerLiteral", "IntegerNegate", "UnionTypeType", "UnionTypeOne", "UnionTypeMixedKinds4", "UnionTypeMixedKinds3", "UnionTypeMixedKinds2", "UnionTypeMixedKinds1", "UnionTypeKind", "UnionTypeEmpty", "UnionConstructorField", "UnionConstructorEmptyField", "TypeAnnotation", "TypeAnnotationFunction", "TypeAnnotationSort", "Text", "TextLiteral", "TextLiteralWithInterpolation", "Double", "DoubleLiteral", "ListFold"]

testGood : IO ()
testGood = testAB Z Z expectPass

main : IO ()
main = do testGood
