module Test

import Idrall.Expr
import Idrall.Check
import Idrall.Parser

stringToExpr : String -> IO (Either () Expr)
stringToExpr x
  = let e = parseExpr x in
    (case e of
          (Left l) => do putStr (show l)
                         pure (Left ())
          (Right r) => do pure (Right r))

exprToValue : Expr -> IO (Either () Value)
exprToValue e
  = let v = eval initEnv e in
    (case v of
          (Left l) => do putStr (show l)
                         pure (Left ())
          (Right r) => do pure (Right r))

checkExpr : Expr -> Value -> IO ()
checkExpr x y
  = let res = check initCtx x y in
    (case res of
          (Left l) => putStrLn (show l)
          (Right r) => putStrLn ("Success"))

testBool : IO ()
testBool = do Right a <- readFile "dhall-lang/tests/type-inference/success/unit/BoolA.dhall"
              Right aExpr <- stringToExpr a
              Right b <- readFile "dhall-lang/tests/type-inference/success/unit/BoolB.dhall"
              Right bExpr <- stringToExpr b
              Right bVal <- exprToValue bExpr
              checkExpr aExpr bVal
