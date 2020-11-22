module Idrall.Error

import Idrall.Value

public export
data Error
  = MissingVar String
  | EvalIntegerNegateErr String
  | EvalNaturalIsZeroErr String
  | EvalBoolAndErr
  | EvalApplyErr
  | Unexpected String Value
  | ErrorMessage String
  | ReadBackError String
  | SortError
  | AssertError String
  | ListAppendError String
  | ListHeadError String
  | FieldNotFoundError String
  | FieldArgMismatchError String
  | InvalidFieldType String
  | CombineError String
  | RecordFieldCollision String
  | ReadFileError String
  | CyclicImportError String

public export
Show Error where
  show (MissingVar x) = "MissingVar: " ++ show x
  show (EvalIntegerNegateErr x) = "EvalIntegerNegateErr:" ++ x
  show (EvalNaturalIsZeroErr x) = "EvalNaturalIsZeroErr:" ++ x
  show EvalBoolAndErr = "EvalBoolAndErr"
  show EvalApplyErr = "EvalApplyErr"
  show (Unexpected str v) = "Unexpected: " ++ str ++ " value: " ++ show v
  show (ErrorMessage x) = "ErrorMessage: " ++ show x
  show (ReadBackError x) = "ReadBackError: " ++ x
  show SortError = "SortError"
  show (AssertError str) = "AssertError: " ++ str
  show (ListAppendError str) = "ListAppendError: " ++ str
  show (ListHeadError str) = "ListHeadError: " ++ str
  show (FieldNotFoundError str) = "FieldNotFoundError: " ++ str
  show (FieldArgMismatchError str) = "FieldArgMismatchError: " ++ str
  show (InvalidFieldType str) = "InvalidFieldType: " ++ str
  show (CombineError str) = "CombineError: " ++ str
  show (RecordFieldCollision str) = "RecordFieldCollision: " ++ str
  show (ReadFileError str) = "ReadFileError: " ++ str
  show (CyclicImportError str) = "CyclicImportError: " ++ str
