module Idrall.Parser.Lexer

import Data.List
import Data.List1

import Text.Lexer
import public Text.Lexer.Tokenizer

public export
data RawToken
  = Ident String
  | Symbol String
  | Keyword String
  | InterpBegin
  | InterpEnd
  | StringLit String
  | White
  | Comment String
  | Unrecognised
  | EndInput

export
Eq RawToken where
  (==) (Ident x) (Ident y) = x == y
  (==) (Symbol x) (Symbol y) = x == y
  (==) (Keyword x) (Keyword y) = x == y
  (==) InterpBegin InterpBegin = True
  (==) InterpEnd InterpEnd = True
  (==) (StringLit x) (StringLit y) = x == y
  (==) White White = True
  (==) (Comment x) (Comment y) =  x == y
  (==) Unrecognised Unrecognised = True
  (==) EndInput EndInput = True
  (==) _ _ = False

export
Show RawToken where
  show (Ident x) = "Ident \{show x}"
  show (Symbol x) = "Symbol \{show x}"
  show (Keyword x) = "Keyword \{show x}"
  show InterpBegin = "InterpBegin"
  show InterpEnd = "InterpEnd"
  show (StringLit x) = "StringLit \{show x}"
  show White = "White"
  show (Comment x) = "Comment \{show x}"
  show Unrecognised = "Unrecognised"
  show EndInput = "EndInput"

public export
TokenKind RawToken where
  TokType (Ident _) = ()
  TokType (Symbol _) = ()
  TokType (Keyword _) = ()
  TokType InterpBegin = ()
  TokType InterpEnd = ()
  TokType (StringLit _) = ()
  TokType White = ()
  TokType (Comment _) = ()
  TokType Unrecognised = String
  TokType EndInput = ()

  tokValue (Ident _) _ = ()
  tokValue (Symbol _) _ = ()
  tokValue (Keyword _) _ = ()
  tokValue InterpBegin _ = ()
  tokValue InterpEnd _ = ()
  tokValue (StringLit _) _ = ()
  tokValue White _ = ()
  tokValue (Comment _) _ = ()
  tokValue Unrecognised x = x
  tokValue EndInput _ = ()

export
Show (Token RawToken) where
  show (Tok (Ident x) _) = "Ident \{show x}"
  show (Tok (Symbol x) _) = "Symbol \{show x}"
  show (Tok (Keyword x) _) = "Keyword \{show x}"
  show (Tok InterpBegin _) = "InterpBegin"
  show (Tok InterpEnd _) = "InterpEnd"
  show (Tok (StringLit x) _) = "StringLit \{show x}"
  show (Tok White _) = "White"
  show (Tok (Comment x) _) = "Comment \{show x}"
  show (Tok (Unrecognised) text) = "Unrecognised \{show $ Token.tokValue Unrecognised text}"
  show (Tok EndInput _) = "EndInput"

public export
TokenRawToken : Type
TokenRawToken = RawToken

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

parseIdent : String -> RawToken
parseIdent x =
  let isKeyword = elem x keywords
      isBuiltin = elem x builtins in
  case (isKeyword, isBuiltin) of
       (True, False) => (Keyword x)
       (False, True) => Ident x -- TODO Builtin
       (_, _) => Ident x

mutual
  ||| The mutually defined functions represent different states in a
  ||| small automaton.
  ||| `toEndComment` is the default state and it will munch through
  ||| the input until we detect a special character (a dash, an
  ||| opening brace, or a double quote) and then switch to the
  ||| appropriate state.
  toEndComment : (k : Nat) -> Recognise (k /= 0)
  toEndComment Z = empty
  toEndComment (S k)
               = some (pred (\c => c /= '-' && c /= '{' && c /= '"'))
                        <+> toEndComment (S k)
             <|> is '{' <+> singleBrace k
             <|> is '-' <+> singleDash k
             <|> stringLit <+> toEndComment (S k)

  ||| After reading a single brace, we may either finish reading an
  ||| opening delimiter or ignore it (e.g. it could be an implicit
  ||| binder).
  singleBrace : (k : Nat) -> Lexer
  singleBrace k
     =  is '-' <+> many (is '-')    -- opening delimiter
               <+> singleDash (S k) -- handles the {----} special case
    <|> toEndComment (S k)          -- not a valid comment

  ||| After reading a single dash, we may either find another one,
  ||| meaning we may have started reading a line comment, or find
  ||| a closing brace meaning we have found a closing delimiter.
  singleDash : (k : Nat) -> Lexer
  singleDash k
     =  is '-' <+> doubleDash k    -- comment or closing delimiter
    <|> is '}' <+> toEndComment k  -- closing delimiter
    <|> toEndComment (S k)         -- not a valid comment

  ||| After reading a double dash, we are potentially reading a line
  ||| comment unless the series of uninterrupted dashes is ended with
  ||| a closing brace in which case it is a closing delimiter.
  doubleDash : (k : Nat) -> Lexer
  doubleDash k = with Prelude.(::)
      many (is '-') <+> choice            -- absorb all dashes
        [ is '}' <+> toEndComment k                      -- closing delimiter
        , many (isNot '\n') <+> toEndComment (S k)       -- line comment
        ]

blockComment : Lexer
blockComment = is '{' <+> is '-' <+> toEndComment 1

stringBegin : Lexer
stringBegin = many (is '#') <+> (is '"')

stringEnd : String
stringEnd = "\""

multilineEnd : String
multilineEnd = "''"

multilineBegin : Lexer
multilineBegin = exact "''"

mutual
  stringTokens : Bool -> Tokenizer RawToken
  stringTokens multi =
    let escapeChars = "\\"
        interpStart = "${"
        escapeLexer = escape (exact escapeChars) any
        charLexer = non $ exact (if multi then multilineEnd else stringEnd)
    in match (someUntil (exact interpStart) (escapeLexer <|> charLexer)) (\x => StringLit x)
       <|> compose (exact interpStart)
                   (const InterpBegin)
                   (const ())
                   (\_ => rawTokens)
                   (const $ is '}')
                   (const InterpEnd)

  rawTokens : Tokenizer RawToken
  rawTokens =
    match blockComment Comment
    <|> match (exact "=") Symbol
    <|> match (exact "&&") Symbol
    <|> match (exact "->") Symbol
    <|> match (exact "(") Symbol
    <|> match (exact ")") Symbol
    <|> match (exact "{") Symbol
    <|> match (exact "}") Symbol
    <|> match (exact "[") Symbol
    <|> match (exact "]") Symbol
    <|> match (exact ",") Symbol
    <|> match (exact ".") Symbol
    <|> match space (const White)
    <|> match ident parseIdent
    <|> match any (const Unrecognised)

{-
rawTokenMap : TokenMap (TokenRawToken)
rawTokenMap =
   [(blockComment, (\x => Tok (Comment x) x))] ++
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
    ]) -- ++ [(ident, (\x => parseIdent x))]
    )
    ++ (toTokenMap $ [ (any, Unrecognised) ])
    -}

{-
export
lexRaw : String -> List (WithBounds TokenRawToken)
lexRaw str =
  let
    (tokens, _, _, _) = lex rawTokenMap str -- those _ contain the source positions
  in
    -- map TokenData.tok tokens
    tokens
    -}

export
lexTo : Lexer ->
        String -> Either (StopReason, Int, Int, String) (List (WithBounds RawToken))
lexTo reject str
    = case lexTo reject rawTokens str of
           -- Add the EndInput token so that we'll have a line and column
           -- number to read when storing spans in the file
           (tok, (EndInput, l, c, _)) => Right (filter notComment tok ++
                                      [MkBounded EndInput False (MkBounds l c l c)])
           (_, fail) => Left fail
    where
      notComment : WithBounds RawToken -> Bool
      notComment t = case t.val of
                          Comment _ => False
                          _ => True

export
lex : String -> Either (StopReason, Int, Int, String) (List (WithBounds RawToken))
lex = lexTo (pred $ const False)
