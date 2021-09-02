module Idrall.Parser.Lexer

import Data.List
import Data.List1

import Text.Lexer
import public Text.Lexer.Tokenizer

public export
data IsMultiline = Multi | Single
Eq IsMultiline where
  (==) Multi Multi = True
  (==) Single Single = True
  (==) _ _ = False

public export
data RawToken
  = Ident String
  | Symbol String
  | Keyword String
  | Builtin String
  | TDouble Double
  | InterpBegin
  | InterpEnd
  | StringBegin IsMultiline
  | StringEnd
  | StringLit String
  | White
  | Comment String
  | Unrecognised
  | EndInput
  | FilePath String

export
Eq RawToken where
  (==) (Ident x) (Ident y) = x == y
  (==) (Symbol x) (Symbol y) = x == y
  (==) (Keyword x) (Keyword y) = x == y
  (==) (Builtin x) (Builtin y) = x == y
  (==) (TDouble x) (TDouble y) = x == y
  (==) InterpBegin InterpBegin = True
  (==) InterpEnd InterpEnd = True
  (==) (StringBegin x) (StringBegin y) = x == y
  (==) StringEnd StringEnd = True
  (==) (StringLit x) (StringLit y) = x == y
  (==) White White = True
  (==) (Comment x) (Comment y) =  x == y
  (==) Unrecognised Unrecognised = True
  (==) EndInput EndInput = True
  (==) (FilePath x) (FilePath y) = x == y
  (==) _ _ = False

export
Show RawToken where
  show (Ident x) = "Ident \{show x}"
  show (Symbol x) = "Symbol \{show x}"
  show (Keyword x) = "Keyword \{show x}"
  show (Builtin x) = "Builtin \{show x}"
  show (TDouble x) = "TDouble \{show x}"
  show InterpBegin = "InterpBegin"
  show InterpEnd = "InterpEnd"
  show (StringBegin x) = "StringBegin"
  show StringEnd = "StringEnd"
  show (StringLit x) = "StringLit \{show x}"
  show White = "White"
  show (Comment x) = "Comment \{show x}"
  show Unrecognised = "Unrecognised"
  show EndInput = "EndInput"
  show (FilePath x) = "FilePath \{show x}"

public export
TokenRawToken : Type
TokenRawToken = RawToken

export
builtins : List String
builtins =
  [ "Type", "Kind", "Sort"
  , "Bool", "True", "False"
  , "Natural", "Natural/build", "Natural/fold", "Natural/isZero", "Natural/even"
  , "Natural/odd", "Natural/subtract", "Natural/toInteger", "Natural/show"
  , "Integer", "Integer/show", "Integer/negate", "Integer/clamp", "Integer/toDouble"
  , "Double", "Double/show"
  , "List/build", "List/fold", "List/length", "List/head"
  , "List/last", "List/indexed", "List/reverse", "List"
  , "Text", "Text/show", "Text/replace"
  , "None"
  , "Optional"
  , "NaN"
  ]

export
keywords : List String
keywords = ["let", "in", "with",
  "if", "then", "else",
  "merge", "toMap", "missing",
  "using", "assert"]

-- variables
ident : Lexer
ident = do
  (pred $ isIdentStart) <+> (many . pred $ isIdentTrailing)
where
  isIdentStart : Char -> Bool
  isIdentStart '_' = True
  isIdentStart x  = isAlpha x || x > chr 160
  isIdentTrailing : Char -> Bool
  isIdentTrailing '_' = True
  isIdentTrailing '/' = True
  isIdentTrailing x = isAlphaNum x || x > chr 160

parseIdent : String -> RawToken
parseIdent x =
  let isKeyword = elem x keywords
      isBuiltin = elem x builtins in
  case (isKeyword, isBuiltin) of
       (True, False) => Keyword x
       (False, True) => Builtin x
       (_, _) => Ident x

-- double
sign : Lexer
sign = is '-' <|> is '+'

exponent : Lexer
exponent = is 'e' <+> opt sign <+> digits

doubleLit : Lexer
doubleLit
    = (opt sign)
      <+> ((digits <+> is '.' <+> digits <+> opt exponent)
           <|> (digits <+> exponent))

-- comments
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

-- imports
embed : Tokenizer RawToken
embed = match (embedStart <+> (someUntil (space) (escapeLexer <|> charLexer))) FilePath
where
  embedStart : Lexer
  embedStart = exact "./" <|> exact "~/" <|> exact "/"
  escapeLexer : Lexer
  escapeLexer = escape (exact "\\") any
  charLexer : Lexer
  charLexer = any

-- strings
stringBegin : Lexer
stringBegin = is '"'

stringEnd : String
stringEnd = "\""

multilineEnd : String
multilineEnd = "''"

mutual
  stringTokens : Bool -> Nat -> Tokenizer RawToken
  stringTokens multi _ =
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
    <|> match (exact "//\\\\") Symbol
    <|> match (exact "//") Symbol
    <|> match (exact "/\\") Symbol
    <|> match (exact "\\") Symbol
    <|> embed
    <|> match (exact "||") Symbol
    <|> match (exact "&&") Symbol
    <|> match (exact "==") Symbol
    <|> match (exact "!=") Symbol
    <|> match (exact "=") Symbol
    <|> match (exact "->") Symbol
    <|> match (exact "++") Symbol
    <|> match (exact "+") Symbol
    <|> match (exact "*") Symbol
    <|> match (exact "#") Symbol
    <|> match (exact "::") Symbol
    <|> match (exact ":") Symbol
    <|> match (exact "?") Symbol
    <|> match (exact "`") Symbol
    <|> match (exact "(") Symbol
    <|> match (exact ")") Symbol
    <|> match (exact "{") Symbol
    <|> match (exact "}") Symbol
    <|> match (exact "[") Symbol
    <|> match (exact "]") Symbol
    <|> match (exact ",") Symbol
    <|> match (exact ".") Symbol
    <|> match (exact "as Text") Keyword
    <|> match space (const White)
    <|> match doubleLit (TDouble . cast)
    <|> match ident parseIdent
    <|> compose stringBegin
                (const $ StringBegin Single)
                (\x => 0)
                (stringTokens False)
                (\hashtag => exact stringEnd <+> reject (is '"'))
                (const StringEnd)
    <|> match any (const Unrecognised)

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
