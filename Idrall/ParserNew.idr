module Idrall.ParserNew

import Data.List

import Text.Parser
import Text.Quantity
import Text.Token
import Text.Lexer

data RawTokenKind
  = Ident
  | Symbol String
  | White
  | Unrecognised

Eq RawTokenKind where
  (==) Ident Ident = True
  (==) (Symbol x) (Symbol y) = x == y
  (==) White White = True
  (==) Unrecognised Unrecognised = True
  (==) _ _ = False

Show RawTokenKind where
  show (Ident) = "Ident"
  show (Symbol x) = "Symbol \{show x}"
  show (White) = "White"
  show (Unrecognised) = "Unrecognised"

TokenKind RawTokenKind where
  TokType Ident = String
  TokType (Symbol _) = ()
  TokType White = ()
  TokType Unrecognised = String

  tokValue Ident x = x
  tokValue (Symbol _) _ = ()
  tokValue White _ = ()
  tokValue Unrecognised x = x

Show (Token RawTokenKind) where
  show (Tok Ident text) = "Ident \{show $ Token.tokValue Ident text}"
  show (Tok (Symbol x) _) = "Symbol \{show $ x}"
  show (Tok White _) = "White"
  show (Tok (Unrecognised) text) = "Unrecognised \{show $ Token.tokValue Unrecognised text}"

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


builtins : List String
builtins = ["True", "False"]

keywords : List String
keywords = ["let", "in"]

parseIdent : String -> Token RawTokenKind
parseIdent x =
  let isKeyword = elem x keywords
      isBuiltin = elem x builtins in
  case (isKeyword, isBuiltin) of
       (True, False) => Tok Ident x -- TODO keyword
       (False, True) => Tok Ident x -- TODO Builtin
       (_, _) => Tok Ident x

rawTokenMap : TokenMap (Token RawTokenKind)
rawTokenMap =
   ((toTokenMap $
    [ (exact "=", Symbol "=")
    , (exact "&&", Symbol "&&")
    , (exact "(", Symbol "(")
    , (exact ")", Symbol ")")
    , (space, White)
    ]) ++ [(ident, (\x => parseIdent x))])
    ++ (toTokenMap $ [ (any, Unrecognised) ])

lexRaw : String -> List (Token RawTokenKind)
lexRaw str =
  let
    (tokens, _, _, _) = lex rawTokenMap str -- those _ contain the source positions
  in
    map TokenData.tok tokens

||| Raw AST representation generated directly from the parser
data Expr a
  = EVar String
  | EBoolLit Bool
  | EBoolAnd (Expr a) (Expr a)
  | ELet String (Expr a) (Expr a)

Show (Expr a) where
  show (EVar x) = "EVar \{show x}"
  show (EBoolLit x) = "EBoolLit \{show x}"
  show (EBoolAnd x y) = "(EBoolAnd \{show x} \{show y})"
  show (ELet x y z) = "TODO"

chainl1 : Grammar (Token RawTokenKind) True (a)
       -> Grammar (Token RawTokenKind) True (a -> a -> a)
       -> Grammar (Token RawTokenKind) True (a)
chainl1 p op = do
  x <- p
  rest x
where
  rest : a -> Grammar (Token RawTokenKind) True (a)
  rest a1 = do
    f <- op
    a2 <- p
    rest (f a1 a2) <|> pure a1

infixOp : Grammar (Token RawTokenKind) True ()
        -> (a -> a -> a)
        -> Grammar (Token RawTokenKind) True (a -> a -> a)
infixOp l ctor = do
  l
  Text.Parser.Core.pure ctor

mutual
  builtinTerm : String -> Grammar (Token RawTokenKind) False (Expr ())
  builtinTerm _ = fail "TODO not implemented"

  boolTerm : String -> Grammar (Token RawTokenKind) False (Expr ())
  boolTerm "True" = pure $ EBoolLit True
  boolTerm "False" = pure $ EBoolLit False
  boolTerm _ = fail "unrecognised const"

  varTerm : Grammar (Token RawTokenKind) True (Expr ())
  varTerm = do
      name <- match Ident
      builtinTerm name <|> boolTerm name <|> toVar (isKeyword name)
  where
    isKeyword : String -> Maybe $ Expr ()
    isKeyword x =
      let isKeyword = elem x keywords
      in case (isKeyword) of
              (True) => Nothing
              (False) => pure $ EVar x
    toVar : Maybe $ Expr () -> Grammar (Token RawTokenKind) False (Expr ())
    toVar Nothing = fail "is reserved word"
    toVar (Just x) = pure x

  atom : Grammar (Token RawTokenKind) True (Expr ())
  atom = varTerm <|> (between (match $ Symbol "(") (match $ Symbol ")") exprTerm)

  boolOp : Grammar (Token RawTokenKind) True (Expr () -> Expr () -> Expr ())
  boolOp = infixOp (match $ Symbol "&&") EBoolAnd

  exprTerm : Grammar (Token RawTokenKind) True (Expr ())
  exprTerm = chainl1 atom boolOp

Show (ParseError (Token RawTokenKind)) where
  show (Error x xs) =
    """
    error: \{x}
    tokens: \{show xs}
    """

doParse : String -> IO ()
doParse input = do
  let tokens = lexRaw input
  putStrLn $ "tokens: " ++ show tokens

  Right (rawTerms, x) <- pure $ parse exprTerm tokens
    | Left e => printLn $ show e
  putStrLn $
    """
    rawTerms: \{show rawTerms}
    x: \{show x}
    """
