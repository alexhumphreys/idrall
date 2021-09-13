module Idrall.Error

import public Idrall.FC

public export
data Error
  = MissingVar FC String
  | AlphaEquivError FC String
  | EvalIntegerNegateErr FC String
  | EvalNaturalIsZeroErr FC String
  | EvalBoolAndErr FC
  | EvalApplyErr FC
  | Unexpected FC String
  | ErrorMessage FC String
  | ReadBackError FC String
  | SortError FC
  | AssertError FC String
  | ListAppendError FC String
  | ListHeadError FC String
  | FieldNotFoundError FC String
  | FieldArgMismatchError FC String
  | InvalidFieldType FC String
  | CombineError FC String
  | RecordFieldCollision FC String
  | ReadFileError FC String
  | MergeUnusedHandler FC String
  | MergeUnhandledCase FC String
  | ToMapError FC String
  | ToMapEmpty FC String
  | EmptyMerge FC String
  | InvalidRecordCompletion FC String
  | CyclicImportError FC String
  | EnvVarError FC String
  | FromDhallError FC String
  | NestedError FC Error Error

public export
Show Error where
  show (MissingVar fc x) = "\{show fc}MissingVar: \{show x}"
  show (AlphaEquivError fc x) = "\{show fc}AlphaEquivError: \{x}"
  show (EvalIntegerNegateErr fc x) = "\{show fc}EvalIntegerNegateErr: \{x}"
  show (EvalNaturalIsZeroErr fc x) = "\{show fc}EvalNaturalIsZeroErr: \{x}"
  show (EvalBoolAndErr fc) = "\{show fc}EvalBoolAndErr"
  show (EvalApplyErr fc) = "\{show fc}EvalApplyErr"
  show (Unexpected fc str) = "\{show fc}Unexpected: \{str}"
  show (ErrorMessage fc x) = "\{show fc}ErrorMessage: \{show x}"
  show (ReadBackError fc x) = "\{show fc}ReadBackError: \{x}"
  show (SortError fc) = "\{show fc}SortError"
  show (AssertError fc str) = "\{show fc}AssertError: \{str}"
  show (ListAppendError fc str) = "\{show fc}ListAppendError: \{str}"
  show (ListHeadError fc str) = "\{show fc}ListHeadError: \{str}"
  show (FieldNotFoundError fc str) = "\{show fc}FieldNotFoundError: \{str}"
  show (FieldArgMismatchError fc str) = "\{show fc}FieldArgMismatchError: \{str}"
  show (InvalidFieldType fc str) = "\{show fc}InvalidFieldType: \{str}"
  show (CombineError fc str) = "\{show fc}CombineError: \{str}"
  show (RecordFieldCollision fc str) = "\{show fc}RecordFieldCollision: \{str}"
  show (ReadFileError fc str) = "\{show fc}ReadFileError: \{str}"
  show (MergeUnusedHandler fc str) = "\{show fc}MergeUnusedHandler: \{str}"
  show (MergeUnhandledCase fc str) = "\{show fc}MergeUnhandledCase: \{str}"
  show (EmptyMerge fc str) = "\{show fc}EmptyMerge: \{str}"
  show (ToMapError fc str) = "\{show fc}ToMapError: \{str}"
  show (ToMapEmpty fc str) = "\{show fc}ToMapEmpty: \{str}"
  show (InvalidRecordCompletion fc str) = "\{show fc}InvalidRecordCompletion: \{str}"
  show (CyclicImportError fc str) = "\{show fc}CyclicImportError: \{str}"
  show (EnvVarError fc str) = "\{show fc}EnvVarError \{show str}"
  show (FromDhallError fc str) = "\{show fc}FromDhallError \{show str}"
  show (NestedError fc e e') = "\{show fc}\{show e}\n\{show e'}"
