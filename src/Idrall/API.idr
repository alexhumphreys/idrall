module Idrall.API

import Idrall.Expr
import Idrall.Value
import Idrall.Error
import Idrall.Check
import Idrall.Parser
import Idrall.Resolve
import Idrall.IOEither
import Idrall.Path

import System.Directory
import Data.List
import Data.Strings

-- Test Stuff

handleError : String -> Error
handleError x = ErrorMessage x

public export
exprFromString : String -> IOEither Error (Expr Void)
exprFromString x = do
  x' <- mapErr (handleError) (liftEither (parseExpr x))
  resolve [] Nothing (fst x')

public export
roundTripEval : String -> IOEither Error Value
roundTripEval x = do
  x' <- exprFromString x
  liftEither (eval initEnv x')

public export
roundTripSynth : String -> IOEither Error Value
roundTripSynth x = do
  x' <- exprFromString x
  liftEither (synth initCtx x')

public export
roundTripCheck : String -> String -> IOEither Error ()
roundTripCheck x y = do
  x' <- exprFromString x
  y' <- roundTripEval y
  liftEither (check initCtx x' y')

public export
showIOEither : Show a => Show b => IOEither a b -> IO String
showIOEither (MkIOEither x) =
  do x' <- x
     case x' of
          (Left l) => pure $ "Error: " ++ show l
          (Right r) => pure $ "Success: " ++ show r

public export
fileErrorHandler : String -> FileError -> Error
fileErrorHandler x y = ErrorMessage x -- ?fileErrorHandler_rhs

public export
doStuff : Show a => Show b => (String -> IOEither a b) -> String -> IO ()
doStuff f x =
  putStrLn !(showIOEither (f x))
