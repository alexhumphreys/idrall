module Test

import Idrall.Expr
import Idrall.Check
import Idrall.Parser

eitherIO : Show a => Either a b -> IO (Either () b)
eitherIO (Left l) = do putStr (show l)
                       pure (Left ())
eitherIO (Right r) = pure (Right r)

stringToExpr : String -> IO (Either () Expr)
stringToExpr x = eitherIO (parseExpr x)

exprToValue : Expr -> IO (Either () Value)
exprToValue e = eitherIO (eval initEnv e)

checkExpr : Expr -> Value -> IO ()
checkExpr x y
  = do res <- eitherIO (check initCtx x y)
       case res of
            (Left l) => pure ()
            (Right r) => putStrLn ("Success")

testBool : IO ()
testBool = do Right a <- readFile "dhall-lang/tests/type-inference/success/unit/BoolA.dhall"
              Right aExpr <- stringToExpr a
              Right b <- readFile "dhall-lang/tests/type-inference/success/unit/BoolB.dhall"
              Right bExpr <- stringToExpr b
              Right bVal <- exprToValue bExpr
              checkExpr aExpr bVal
