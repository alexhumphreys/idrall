module Idrall.Pretty

import Data.String

import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Util
import Text.PrettyPrint.Prettyprinter.Doc

import Idrall.Expr
import Idrall.Path

prettyDottedList : Pretty a => List a -> Doc ann
prettyDottedList [] = pretty ""
prettyDottedList (x :: []) = pretty x
prettyDottedList (x :: xs) = pretty x <+> pretty "." <+> prettyDottedList xs

sbraces : Doc ann -> Doc ann
sbraces = enclose lbrace (space <+> rbrace)

mutual
  prettySortedMap : Pretty x => Pretty y
                  => (Doc ann -> Doc ann)
                  -> Doc ann
                  -> (SortedMap x y)
                  -> Doc ann
  prettySortedMap wrapping sign e =
    let ls = SortedMap.toList e
        lsDoc = map (go sign) ls
    in
    wrapping $ foldl (<++>) neutral (punctuate comma lsDoc)
  where
    go : Doc ann -> (x, y) -> Doc ann
    go x (s, e) = pretty s <++> x <++> pretty e

  prettyUnion : Pretty x => Pretty y
              => (SortedMap x (Maybe y))
              -> Doc ann
  prettyUnion e =
    let ls = SortedMap.toList e
        lsDoc = map go ls
    in
    enclose langle (space <++> rangle) $ foldl (<++>) neutral (punctuate (space <+> pipe) lsDoc)
  where
    go : (x, Maybe y) -> Doc ann
    go (s, Nothing) = pretty s
    go (s, Just e) = pretty s <++> colon <++> pretty e

  export
  Pretty U where
    pretty CType = "Type"
    pretty Sort = "Sort"
    pretty Kind = "Kind"

  export
  Pretty FieldName where
    pretty (MkFieldName x) = pretty x

  export
  Pretty FilePath where
    pretty (MkFilePath path Nothing) = pretty $ prettyPrintPath path
    pretty (MkFilePath path (Just x)) =
      (pretty $ prettyPrintPath path) <+> pretty "/" <+> pretty x

  export
  Pretty ImportStatement where
    pretty (LocalFile x) = pretty x
    pretty (EnvVar x) = pretty "env:" <+> pretty x
    pretty (Http x) = pretty x
    pretty Missing = pretty "Missing"

  export
  Pretty a => Pretty (Import a) where
    pretty (Raw x) = pretty x
    pretty (Text x) = pretty x <++> pretty "as Text"
    pretty (Location x) = pretty x <++> pretty "as Location"
    pretty (Resolved x) = pretty "ERROR: SHOULD NOT BE"

  export
  Pretty a => Pretty (Chunks a) where
    pretty (MkChunks [] x) = dquotes $ pretty x
    pretty (MkChunks (y :: xs) x) = dquotes $ pretty y <+> pretty xs <+> pretty x


  export
  Pretty a => Pretty (Expr a) where
    pretty (EConst fc x) = pretty x
    pretty (EVar fc x n) = pretty x <+> pretty "@" <+> pretty n
    pretty (EApp fc x y) = pretty x <++> pretty y
    pretty (ELam fc n x y) =
      pretty "\\" <+> parens (pretty n <++> colon <++> pretty x)
        <++> pretty "->" <++> pretty y
    pretty (EPi fc "_" x y) = pretty x <++> pretty "->" <++> pretty y
    pretty (EPi fc n x y) =
      pretty "forall" <+> parens (pretty n <++> colon <++> pretty x)
        <++> pretty "->" <++> pretty y
    pretty (ELet fc x t y z) =
      pretty "let" <++> pretty x <++> equals <++> pretty y
        <++> pretty "in" <++> pretty z
    pretty (EAnnot fc x y) = pretty x <++> colon <++> pretty y
    pretty (EBool fc) = pretty "Bool"
    pretty (EBoolLit fc x) = pretty $ show x
    pretty (EBoolAnd fc x y) = pretty x <++> pretty "&&" <++> pretty y
    pretty (EBoolOr fc x y) = pretty x <++> pretty "||" <++> pretty y
    pretty (EBoolEQ fc x y) = pretty x <++> pretty "==" <++> pretty y
    pretty (EBoolNE fc x y) = pretty x <++> pretty "!=" <++> pretty y
    pretty (EBoolIf fc x y z) =
      pretty "if" <++> pretty x
      <++> pretty "then" <++> pretty y
      <++> pretty "else" <++> pretty z
    pretty (ENatural fc) = pretty "Natural"
    pretty (ENaturalLit fc x) = pretty x
    pretty (ENaturalBuild fc) = pretty "Natural/build"
    pretty (ENaturalFold fc) = pretty "Natural/fold"
    pretty (ENaturalIsZero fc) = pretty "Natural/isZero"
    pretty (ENaturalEven fc) = pretty "Natural/Even"
    pretty (ENaturalOdd fc) = pretty "Natural/Odd"
    pretty (ENaturalSubtract fc) = pretty "Natural/subtract"
    pretty (ENaturalToInteger fc) = pretty "Natural/toInteger"
    pretty (ENaturalShow fc) = pretty "Natural/show"
    pretty (ENaturalPlus fc x y) = pretty x <++> pretty "+" <++> pretty y
    pretty (ENaturalTimes fc x y) = pretty x <++> pretty "*" <++> pretty y
    pretty (EInteger fc) = pretty "Integer"
    pretty (EIntegerLit fc x) = pretty x
    pretty (EIntegerShow fc) = pretty "Integer/show"
    pretty (EIntegerNegate fc) = pretty "Integer/negate"
    pretty (EIntegerClamp fc) = pretty "Integer/clamp"
    pretty (EIntegerToDouble fc) = pretty "Integer/toDouble"
    pretty (EDouble fc) = pretty "Double"
    pretty (EDoubleLit fc x) = pretty $ show x
    pretty (EDoubleShow fc) = pretty "Double/show"
    pretty (EList fc) = pretty "List"
    pretty (EListLit fc t xs) = pretty xs <++> colon <++> pretty t
    pretty (EListAppend fc x y) = pretty x <++> pretty "#" <++> pretty y
    pretty (EListBuild fc) = pretty "List/build"
    pretty (EListFold fc) = pretty "List/fold"
    pretty (EListLength fc) = pretty "List/length"
    pretty (EListHead fc) = pretty "List/head"
    pretty (EListLast fc) = pretty "List/last"
    pretty (EListIndexed fc) = pretty "List/indexed"
    pretty (EListReverse fc) = pretty "List/indexed"
    pretty (EText fc) = pretty "Text"
    pretty (ETextLit fc cs) = pretty cs
    pretty (ETextAppend fc x y) = pretty x <++> pretty "++" <++> pretty y
    pretty (ETextShow fc) = pretty "Text/show"
    pretty (ETextReplace fc) = pretty "Text/replace"
    pretty (EOptional fc) = pretty "Optional"
    pretty (ESome fc x) = pretty "Some" <++> pretty x
    pretty (ENone fc) = pretty "None"
    pretty (EField fc x y) =
      pretty x <+> pretty "." <+> pretty y
    pretty (EWith fc x xs y) =
      pretty x <++> pretty "with" <++>
      prettyDottedList (forget xs) <++> equals <++> pretty y
    pretty (EEquivalent fc x y) = pretty x <++> pretty "===" <++> pretty y
    pretty (EAssert fc x) = pretty "assert" <++> colon <++> pretty x
    pretty (ERecord fc x) = prettySortedMap sbraces colon x
    pretty (ERecordLit fc x) = prettySortedMap sbraces equals x
    pretty (EUnion fc x) = prettyUnion x
    pretty (ECombine fc x y) = pretty x <++> pretty "/\\" <++> pretty y
    pretty (ECombineTypes fc x y) = pretty x <++> pretty "//\\\\" <++> pretty y
    pretty (EPrefer fc x y) = pretty x <++> pretty "//" <++> pretty y
    pretty (ERecordCompletion fc x y) = pretty x <++> pretty "::" <++> pretty y
    pretty (EMerge fc x y Nothing) = pretty "merge" <++> pretty x <++> pretty y
    pretty (EMerge fc x y (Just z)) = pretty "merge" <++> pretty x <++> pretty y <++> pretty ":" <++> pretty z
    pretty (EToMap fc x Nothing) = pretty "toMap" <++> pretty x
    pretty (EProject fc x (Left y)) = pretty x <+> dot <+> braces (pretty y) -- TODO fix
    pretty (EProject fc x (Right y)) = pretty x <+> dot <+> parens (pretty y)
    pretty (EToMap fc x (Just y)) =
      pretty "merge" <++> pretty x
      <++> pretty ":" <++> pretty y
    pretty (EImportAlt fc x y) = pretty x <++> pretty "?" <++> pretty y
    pretty (EEmbed fc x) = pretty x
