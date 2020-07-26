module Idrall.Error

import Idrall.Value

%hide Error

public export
data Error
  = MissingVar String
  | EvalNaturalIsZeroErr String
  | EvalBoolAndErr
  | EvalApplyErr
  | Unexpected String Value
  | ErrorMessage String
  | ReadBackError String
  | SortError
  | AssertError String
  | ListAppendError String
  | ReadFileError String
  | CyclicImportError String

public export
Show Error where
  show (MissingVar x) = "MissingVar: " ++ show x
  show (EvalNaturalIsZeroErr x) = "EvalNaturalIsZero error:" ++ x
  show EvalBoolAndErr = "EvalBoolAndErr"
  show EvalApplyErr = "EvalApplyErr"
  show (Unexpected str v) = "Unexpected: " ++ str ++ " value: " ++ show v
  show (ErrorMessage x) = "ErrorMessage: " ++ show x
  show (ReadBackError x) = "ReadBackError: " ++ x
  show SortError = "SortError"
  show (AssertError str) = "AssertError: " ++ str
  show (ListAppendError str) = "ListAppendError: " ++ str
  show (ReadFileError str) = "ReadFileError: " ++ str
  show (CyclicImportError str) = "CyclicImportError: " ++ str
