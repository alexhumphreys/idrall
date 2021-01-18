module Idrall.APIv1

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

export
resolveFromString : Maybe FilePath -> String -> IOEither Error (Expr Void)
resolveFromString path x = do
  x' <- mapErr (handleError) (liftEither (parseExpr x))
  resolve [] path (fst x')

public export
roundTripEval : String -> IOEither Error Value
roundTripEval x = do
  x' <- exprFromString x
  liftEither (eval Empty x')

public export
roundTripSynth : String -> IOEither Error (Expr Void, Value)
roundTripSynth x = do
  x' <- exprFromString x
  liftEither (infer initCxt x')

public export
roundTripCheck : String -> String -> IOEither Error ()
roundTripCheck x y = do
  x' <- exprFromString x
  y' <- roundTripEval y
  liftEither (check initCxt x' y')
  pure ()

public export
roundTripCheck' : Maybe FilePath -> String -> String -> IOEither Error ()
roundTripCheck' path x y = do
  x' <- resolveFromString path x
  y' <- roundTripEval y
  liftEither (check initCxt x' y')
  pure ()

public export
valueFromString : String -> IOEither Error Value
valueFromString x = do
  roundTripSynth x
  roundTripEval x

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
