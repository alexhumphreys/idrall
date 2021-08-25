module Idrall.Parser.Lexer

import Data.List
import Data.List1

import Text.Parser
import Text.Quantity
import Text.Token
import Text.Lexer
import Text.Bounded

public export
data RawToken
  = Ident
  | Symbol String
  | Keyword String
  | White
  | Unrecognised

export
Eq RawToken where
  (==) Ident Ident = True
  (==) (Symbol x) (Symbol y) = x == y
  (==) (Keyword x) (Keyword y) = x == y
  (==) White White = True
  (==) Unrecognised Unrecognised = True
  (==) _ _ = False

export
Show RawToken where
  show (Ident) = "Ident"
  show (Symbol x) = "Symbol \{show x}"
  show (Keyword x) = "Keyword \{show x}"
  show (White) = "White"
  show (Unrecognised) = "Unrecognised"

public export
TokenKind RawToken where
  TokType Ident = String
  TokType (Symbol _) = ()
  TokType (Keyword _) = ()
  TokType White = ()
  TokType Unrecognised = String

  tokValue Ident x = x
  tokValue (Symbol _) _ = ()
  tokValue (Keyword _) _ = ()
  tokValue White _ = ()
  tokValue Unrecognised x = x

export
Show (Token RawToken) where
  show (Tok Ident text) = "Ident \{show $ Token.tokValue Ident text}"
  show (Tok (Symbol x) _) = "Symbol \{show $ x}"
  show (Tok (Keyword x) _) = "Keyword \{show $ x}"
  show (Tok White _) = "White"
  show (Tok (Unrecognised) text) = "Unrecognised \{show $ Token.tokValue Unrecognised text}"

public export
TokenRawToken : Type
TokenRawToken = Token RawToken

isIdentStart : Char -> Bool
isIdentStart '_' = True
isIdentStart x  = isAlpha x || x > chr 160

isIdentTrailing : Char -> Bool
isIdentTrailing '_' = True
isIdentTrailing '/' = True
isIdentTrailing x = isAlphaNum x || x > chr 160

export %inline
isIdent : String -> Bool
isIdent string =
  case unpack string of
    []      => False
    (x::xs) => isIdentStart x && all (isIdentTrailing) xs

ident : Lexer
ident = do
  (pred $ isIdentStart) <+> (many . pred $ isIdentTrailing)


export
builtins : List String
builtins = ["True", "False"]

export
keywords : List String
keywords = ["let", "in", "with"]

parseIdent : String -> TokenRawToken
parseIdent x =
  let isKeyword = elem x keywords
      isBuiltin = elem x builtins in
  case (isKeyword, isBuiltin) of
       (True, False) => Tok (Keyword x) x
       (False, True) => Tok Ident x -- TODO Builtin
       (_, _) => Tok Ident x

rawTokenMap : TokenMap (TokenRawToken)
rawTokenMap =
   ((toTokenMap $
    [ (exact "=", Symbol "=")
    , (exact "&&", Symbol "&&")
    , (exact "->", Symbol "->")
    , (exact "(", Symbol "(")
    , (exact ")", Symbol ")")
    , (exact "{", Symbol "{")
    , (exact "}", Symbol "}")
    , (exact "[", Symbol "[")
    , (exact "]", Symbol "]")
    , (exact ",", Symbol ",")
    , (exact ".", Symbol ".")
    , (space, White)
    ]) ++ [(ident, (\x => parseIdent x))])
    ++ (toTokenMap $ [ (any, Unrecognised) ])

export
lexRaw : String -> List (WithBounds TokenRawToken)
lexRaw str =
  let
    (tokens, _, _, _) = lex rawTokenMap str -- those _ contain the source positions
  in
    -- map TokenData.tok tokens
    tokens
