module Test

import Idrall.Expr
import Idrall.Check
import Idrall.Parser

testBool : IO ()
testBool = do Right a <- readFile "dhall-lang/tests/type-inference/success/unit/BoolA.dhall" |
                Left x => putStr "foo"
              -- Right aExpr <- parseExpr a | Left b => putStr "error"
              ?foo
