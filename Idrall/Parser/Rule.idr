module Idrall.Parser.Rule

import Data.List
import Data.List1
import Data.String

import Text.Parser
import Text.Quantity
import Text.Token
import Text.Lexer
import Text.Bounded

import Idrall.Parser.Lexer
import Idrall.Expr
import Idrall.Path

public export
Rule : {state : Type} -> Type -> Type
Rule ty = Grammar state RawToken True ty

public export
EmptyRule : {state : Type} -> Type -> Type
EmptyRule ty = Grammar state RawToken False ty

export
whitespace : Rule ()
whitespace =
  terminal ("Expected whitespace") $
    \case
      White => Just ()
      _ => Nothing

export
tokenW : Grammar state (TokenRawToken) True a -> Grammar state (TokenRawToken) True a
tokenW p = do
  x <- p
  _ <- optional whitespace
  pure x

export
keyword : String -> Rule ()
keyword req =
  terminal ("Expected '" ++ req ++ "'") $
    \case
      Keyword s => if s == req then Just () else Nothing
      _ => Nothing

export
symbol : String -> Rule ()
symbol req =
  terminal ("Expected '" ++ req ++ "'") $
    \case
      Symbol s => if s == req then Just () else Nothing
      _ => Nothing

export
textBegin : Rule IsMultiline
textBegin =
  terminal "expected \" or ''" $
    \case
      StringBegin x => Just x
      _ => Nothing

export
textBoundary : Rule ()
textBoundary =
  terminal "expected \" or ''" $
    \case
      StringBegin _ => Just ()
      StringEnd => Just ()
      _ => Nothing

escapeSingle : List Char -> List Char -> Maybe (List Char)
escapeSingle escapeChars [] = pure []
escapeSingle escapeChars (x :: xs) =
  if isPrefixOf escapeChars (x :: xs)
  then case drop (length escapeChars) (x::xs) of
       ('b' :: xs) => pure $ '\b' :: !(escapeSingle escapeChars xs)
       ('f' :: xs) => escapeSingle escapeChars ('\f' :: xs)
       ('n' :: xs) => escapeSingle escapeChars ('\n' :: xs)
       ('r' :: xs) => escapeSingle escapeChars ('\r' :: xs)
       ('t' :: xs) => escapeSingle escapeChars ('\t' :: xs)
       ('"' :: xs) => escapeSingle escapeChars ('"' :: xs)
       ('$' :: xs) => escapeSingle escapeChars ('$' :: xs)
       ('\\' :: xs) => escapeSingle escapeChars ('\\' :: xs)
       ('/' :: xs) => escapeSingle escapeChars ('/' :: xs)
       -- TODO unicode
       _ => pure $ x :: !(escapeSingle escapeChars xs)
  else Just $ x :: !(escapeSingle escapeChars xs)

escape : IsMultiline -> String -> Maybe String
escape Single str = Just $ pack $ !(escapeSingle ['\\'] $ unpack str)
escape Multi str = Just $ str

export
textLit : IsMultiline -> Rule String
textLit x =
  terminal "expected valid Text" $
    \case
      StringLit str => escape x str
      _ => Nothing

export
interpBegin : Rule ()
interpBegin =
  terminal "expected ${" $
    \case
      InterpBegin => Just ()
      _ => Nothing

export
interpEnd : Rule ()
interpEnd =
  terminal "expected }" $
    \case
      InterpEnd => Just ()
      _ => Nothing

export
identPart : Rule String
identPart =
  terminal "expected name" $
    \case
      Ident x => Just x
      _ => Nothing

export
fieldName : Rule String
fieldName =
  terminal "expected fieldName" $
    \case
      Ident x => Just x
      Builtin x => Just x
      _ => Nothing

export
missingImport : Rule ()
missingImport =
  terminal "expected missing" $
    \case
      MissingImport => Just ()
      _ => Nothing

export
httpImport : Rule String
httpImport =
  terminal "expected http import" $
    \case
      HttpImport x => Just x
      _ => Nothing

export
envImport : Rule String
envImport =
  terminal "expected env import" $
    \case
      EnvImport x => Just x
      _ => Nothing

export
arrow : Rule ()
arrow = tokenW $ symbol "->" <|> symbol "→"

export
shaImport : Rule String
shaImport =
  terminal "expected sha import" $
    \case
      Sha x => Just x -- TODO remove `sha:` prefix
      _ => Nothing

export
filePath : Rule Path
filePath =
  terminal "expected import path" $
    \case
      RelImport x => Just $ Relative $ forget $ split (== '/') x
      AbsImport x => Just $ Absolute $ forget $ split (== '/') x
      HomeDirImport x => Just $ Home $ forget $ split (== '/') x
      _ => Nothing

export
naturalLit : Rule Nat
naturalLit =
  terminal "expected natural" $
    \case
      TNatural x => Just x
      _ => Nothing

export
integerLit : Rule Integer
integerLit =
  terminal "expected integer" $
    \case
      TInteger x => Just x
      _ => Nothing

export
doubleLit : Rule Double
doubleLit =
  terminal "expected double" $
    \case
      TDouble x => Just x
      _ => Nothing

export
dottedList : Rule (List1 FieldName)
dottedList = do
  _ <- optional whitespace
  x <- sepBy1 (tokenW $ symbol ".") (identPart)
  pure $ map MkFieldName x

export
dottedListRec : Rule (List1 FieldName)
dottedListRec = do
  _ <- optional whitespace
  x <- sepBy1 (tokenW $ symbol ".") (fieldName)
  pure $ map MkFieldName x


export
builtin : Rule String
builtin =
  terminal "expected builtin" $
    \case
      Builtin x => Just x
      _ => Nothing

export
someBuiltin : Rule ()
someBuiltin =
  terminal "expected builtin" $
    \case
      Builtin "Some" => Just ()
      _ => Nothing

export
endOfInput : Rule ()
endOfInput =
  terminal "expected builtin" $
    \case
      EndInput => Just ()
      _ => Nothing
