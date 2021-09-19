module Idrall.Error

import public Text.PrettyPrint.Prettyprinter
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
  | ParseError FC String
  | LexError FC String
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
  show (ParseError fc str) = "\{show fc}ParseError \{show str}"
  show (LexError fc str) = "\{show fc}LexError \{show str}"
  show (NestedError fc e e') = "\{show fc}\{show e}\n\{show e'}"

export
Pretty Error where
  pretty (MissingVar fc x) = pretty fc <++> hardline <+> pretty "Missing Var" <++> colon <++> pretty (show x)
  pretty (AlphaEquivError fc x) = pretty fc <++> hardline <+> pretty "AlphaEquivError" <++> colon <++> pretty (show x)
  pretty (EvalIntegerNegateErr fc x) = pretty fc <++> hardline <+> pretty "EvalIntegerNegateErr" <++> colon <++> pretty (show x)
  pretty (EvalNaturalIsZeroErr fc x) = pretty fc <++> hardline <+> pretty "EvalNaturalIsZeroErr" <++> colon <++> pretty (show x)
  pretty (EvalBoolAndErr fc) = pretty fc <++> hardline <+> pretty "EvalBoolAndErr"
  pretty (EvalApplyErr fc) = pretty fc <++> hardline <+> pretty "EvalApplyErr"
  pretty (Unexpected fc x) = pretty fc <++> hardline <+> pretty "Unexpected" <++> colon <++> pretty (show x)
  pretty (ErrorMessage fc x) = pretty fc <++> hardline <+> pretty "ErrorMessage" <++> colon <++> pretty (show x)
  pretty (ReadBackError fc x) = pretty fc <++> hardline <+> pretty "ReadBackError" <++> colon <++> pretty (show x)
  pretty (SortError fc) = pretty fc <++> hardline <+> pretty "SortError"
  pretty (AssertError fc x) = pretty fc <++> hardline <+> pretty "AssertError" <++> colon <++> pretty (show x)
  pretty (ListAppendError fc x) = pretty fc <++> hardline <+> pretty "ListAppendError" <++> colon <++> pretty (show x)
  pretty (ListHeadError fc x) = pretty fc <++> hardline <+> pretty "ListHeadError" <++> colon <++> pretty (show x)
  pretty (FieldNotFoundError fc x) = pretty fc <++> hardline <+> pretty "FieldNotFoundError" <++> colon <++> pretty (show x)
  pretty (FieldArgMismatchError fc x) = pretty fc <++> hardline <+> pretty "FieldArgMismatchError" <++> colon <++> pretty (show x)
  pretty (InvalidFieldType fc x) = pretty fc <++> hardline <+> pretty "InvalidFieldType" <++> colon <++> pretty (show x)
  pretty (CombineError fc x) = pretty fc <++> hardline <+> pretty "CombineError" <++> colon <++> pretty (show x)
  pretty (RecordFieldCollision fc x) = pretty fc <++> hardline <+> pretty "RecordFieldCollision" <++> colon <++> pretty (show x)
  pretty (ReadFileError fc x) = pretty fc <++> hardline <+> pretty "ReadFileError" <++> colon <++> pretty (show x)
  pretty (MergeUnusedHandler fc x) = pretty fc <++> hardline <+> pretty "MergeUnusedHandler" <++> colon <++> pretty (show x)
  pretty (MergeUnhandledCase fc x) = pretty fc <++> hardline <+> pretty "MergeUnhandledCase" <++> colon <++> pretty (show x)
  pretty (ToMapError fc x) = pretty fc <++> hardline <+> pretty "ToMapError" <++> colon <++> pretty (show x)
  pretty (ToMapEmpty fc x) = pretty fc <++> hardline <+> pretty "ToMapEmpty" <++> colon <++> pretty (show x)
  pretty (EmptyMerge fc x) = pretty fc <++> hardline <+> pretty "EmptyMerge" <++> colon <++> pretty (show x)
  pretty (InvalidRecordCompletion fc x) = pretty fc <++> hardline <+> pretty "InvalidRecordCompletion" <++> colon <++> pretty (show x)
  pretty (CyclicImportError fc x) = pretty fc <++> hardline <+> pretty "CyclicImportError" <++> colon <++> pretty (show x)
  pretty (EnvVarError fc x) = pretty fc <++> hardline <+> pretty "EnvVarError" <++> colon <++> pretty (show x)
  pretty (FromDhallError fc x) = pretty fc <++> hardline <+> pretty "FromDhallError" <++> colon <++> pretty (show x)
  pretty (ParseError fc x) = pretty fc <++> hardline <+> pretty "ParseError" <++> colon <++> pretty (show x)
  pretty (LexError fc x) = pretty fc <++> hardline <+> pretty "LexError" <++> colon <++> pretty (show x)
  pretty (NestedError fc x y) = pretty fc <++> hardline <+> pretty "NestedError" <++> colon <++> pretty (show x)
