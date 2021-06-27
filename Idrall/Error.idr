module Idrall.Error

public export
data Error
  = MissingVar String
  | AlphaEquivError String
  | EvalIntegerNegateErr String
  | EvalNaturalIsZeroErr String
  | EvalBoolAndErr
  | EvalApplyErr
  | Unexpected String
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
  | MergeUnusedHandler String
  | MergeUnhandledCase String
  | ToMapError String
  | ToMapEmpty String
  | EmptyMerge String
  | InvalidRecordCompletion String
  | CyclicImportError String
  | EnvVarError String
  | FromDhallError String
  | NestedError Error Error

public export
Show Error where
  show (MissingVar x) = "MissingVar: " ++ show x
  show (AlphaEquivError x) = "AlphaEquivError:" ++ x
  show (EvalIntegerNegateErr x) = "EvalIntegerNegateErr:" ++ x
  show (EvalNaturalIsZeroErr x) = "EvalNaturalIsZeroErr:" ++ x
  show EvalBoolAndErr = "EvalBoolAndErr"
  show EvalApplyErr = "EvalApplyErr"
  show (Unexpected str) = "Unexpected: " ++ str
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
  show (MergeUnusedHandler str) = "MergeUnusedHandler: " ++ str
  show (MergeUnhandledCase str) = "MergeUnhandledCase: " ++ str
  show (EmptyMerge str) = "EmptyMerge: " ++ str
  show (ToMapError str) = "ToMapError: " ++ str
  show (ToMapEmpty str) = "ToMapEmpty: " ++ str
  show (InvalidRecordCompletion str) = "InvalidRecordCompletion: " ++ str
  show (CyclicImportError str) = "CyclicImportError: " ++ str
  show (EnvVarError str) = "EnvVarError " ++ show str
  show (FromDhallError str) = "FromDhallError " ++ show str
  show (NestedError e e') =
    show e ++ "\n" ++ show e'
