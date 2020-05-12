module Test

import Idrall.Expr
import Idrall.Check
import Idrall.Parser

readAB : String -> String -> IO (String, String)
readAB a b =
  do Right fa <- readFile a
     Right fb <- readFile b
     pure (fa, fb)

inferAB : (String, String) -> IO ()
inferAB (a, b) =
  let ea = parseExpr a
      eb = parseExpr b
  in
  (case ea of
        (Left l) => putStr l
        (Right exp) => (case eb of
                             (Left l) => putStr l
                             (Right act) => ?inferAB_rhs_2))
-- Right ea <- parseExpr a | Left s => putStr s

testBool : IO ()
testBool = do c <- readAB "dhall-lang/tests/type-inference/success/unit/BoolA.dhall" "dhall-lang/tests/type-inference/success/unit/BoolB.dhall"
              ?fo
