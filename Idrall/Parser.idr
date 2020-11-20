module Idrall.Parser

import Control.Monad.Identity
import Control.Monad.Trans

import Data.Fin
import Data.Nat
import Data.Strings
import Data.List1
import Data.String.Parser
import Data.String.Parser.Expression

import Idrall.Lexer
import Idrall.Expr
import Idrall.Path
import Idrall.ParserPR

%hide Data.String.Parser.char
%hide Prelude.pow

||| Succeeds if the next char is `c`
char : Applicative m => Char -> ParseT m Char
char c = satisfy (== c)

string' : Monad m => String -> ParseT m String
string' str = do string str
                 pure str

fIntegerNegate : (Expr ImportStatement)
fIntegerNegate = ELam "integerNegateParam1" EInteger (EIntegerNegate (EVar "integerNegateParam1"))

fNaturalIsZero : (Expr ImportStatement)
fNaturalIsZero = ELam "naturalIsZeroParam1" ENatural (ENaturalIsZero (EVar "naturalIsZeroParam1"))

fList : (Expr ImportStatement)
fList = ELam "listArg1" (EConst CType) (EList (EVar "listArg1"))

fListHead : (Expr ImportStatement)
fListHead = ELam "listHeadArg1" (EConst CType)
              (ELam "listHeadArg2" (EList (EVar "listHeadArg1"))
                (EListHead (EVar "listHeadArg1") (EVar "listHeadArg2")))

fOptional : (Expr ImportStatement)
fOptional = ELam "optionalArg1" (EConst CType) (EOptional (EVar "optionalArg1"))

fNone : (Expr ImportStatement)
fNone = ELam "noneArg1" (EConst CType) (ENone (EVar "noneArg1"))

builtin : Parser (Expr ImportStatement)
builtin =
  (string "Integer/negate" *> pure fIntegerNegate) <|>
  (string "Natural/isZero" *> pure fNaturalIsZero) <|>
  (string "List/head" *> pure fListHead) <|>
  (string "List" *> pure fList) <|>
  (string "None" *> pure fNone) <|>
  (string "Optional" *> pure fOptional)

true : Parser (Expr ImportStatement)
true = token "True" *> pure (EBoolLit True)

false : Parser (Expr ImportStatement)
false = token "False" *> pure (EBoolLit False)

bool : Parser (Expr ImportStatement)
bool = token "Bool" *> pure (EBool)

text : Parser (Expr ImportStatement)
text = token "Text" *> pure (EText)

integer : Parser (Expr ImportStatement)
integer = token "Integer" *> pure (EInteger)

integerLit : Parser (Expr ImportStatement)
integerLit = do op <- (char '-' <|> char '+')
                x <- some digit
                case op of
                     '+' => pure (EIntegerLit (getInteger x))
                     '-' => pure (EIntegerLit ((getInteger x)*(-1)))
                     _ => fail "not an Integer"
where getInteger : List (Fin 10) -> Integer
      getInteger = foldl (\a => \b => 10 * a + cast b) 0

natural : Parser (Expr ImportStatement)
natural = token "Natural" *> pure (ENatural)

double : Parser (Expr ImportStatement)
double = token "Double" *> pure (EDouble)

naturalLit : Parser (Expr ImportStatement)
naturalLit = do n <- some digit
                pure (ENaturalLit (getNatural n))
where getNatural : List (Fin 10) -> Nat
      getNatural = foldl (\a => \b => 10 * a + cast b) 0

-- From lightyear JSON parser
record Scientific where
  constructor MkScientific
  coefficient : Integer
  exponent : Integer

-- parses "2.3" as 2.3000000000000003
-- but "2.31" as 2.31
scientificToDouble : Scientific -> Double
scientificToDouble (MkScientific c e) = (fromInteger c) * exp
  where
    pow' : (Num a) => a -> Nat -> a
    pow' x Z = 1
    pow' x (S n) = x * (pow' x n)
    fromIntegerNat : Integer -> Nat
    fromIntegerNat 0 = Z
    fromIntegerNat n =
      if (n > 0) then
        S (fromIntegerNat (assert_smaller n (n - 1)))
      else
        Z
    exp : Double
    exp = if e < 0 then 1 / pow' 10 (fromIntegerNat (- e))
                   else pow' 10 (fromIntegerNat e)

parseScientific : Parser Scientific
parseScientific = do sign <- maybe 1 (const (-1)) `map` optional (char '-') -- TODO handle '+'
                     digits <- some digit
                     char '.'
                     decimals <- some digit
                     hasExponent <- isJust `map` optional (char 'e')
                     exponent <- if hasExponent then integer else pure 0
                     pure $ MkScientific (sign * fromDigits (digits ++ decimals))
                                         (exponent - cast (length decimals))
  where fromDigits : List (Fin 10) -> Integer
        fromDigits = foldl (\a, b => 10 * a + cast b) 0

doubleLit : Parser (Expr ImportStatement)
doubleLit = do k <- map scientificToDouble parseScientific
               pure (EDoubleLit k)

type : Parser (Expr ImportStatement)
type = token "Type" *> pure (EConst CType)

kind : Parser (Expr ImportStatement)
kind = token "Kind" *> pure (EConst Kind)

sort : Parser (Expr ImportStatement)
sort = token "Sort" *> pure (EConst Sort)

identFirst : Parser Char
identFirst = letter <|> char '_'

identRest : Parser Char
identRest = alphaNum <|> char '-' <|> char '/' <|> char '_'

-- TODO identBackticks : Parser String

identLong : Parser String
identLong = do f <- identFirst
               r <- some identRest
               pure (pack (f :: r))

identShort : Parser String
identShort = do i <- identFirst
                pure (singleton i)

reservedNames' : List String
reservedNames' =
  [ "in", "let", "assert"
  , "->", "&&", ":"
  , "List", "Text", "Optional", "Natural", "Integer", "Double"
  , "Some", "None"
  , "Type", "Kind", "Sort"]

parseAny : List String -> Parser ()
parseAny [] = fail "emptyList" -- TODO use List1 in idris2 to remove this case
parseAny (x :: xs) = string x <|> (parseAny xs)

reservedNames : Parser ()
reservedNames = do
  parseAny reservedNames'
  (do space; pure ()) <|> eos

identity : Parser String
identity = do
  _ <- requireFailure reservedNames
  (identLong <|> identShort) <* spaces

var : Parser (Expr ImportStatement)
var = do i <- identity
         pure (EVar i)

appl : Parser ((Expr ImportStatement) -> (Expr ImportStatement) -> (Expr ImportStatement))
appl = do spaces
          pure EApp

field : Parser ((Expr ImportStatement) -> (Expr ImportStatement))
field = do
  token "."
  i <- identity
  pure (\e => (EField e (MkFieldName i)))

table : OperatorTable (Expr ImportStatement)
table = [ [ Postfix field]
        , [ Infix appl AssocLeft]
        , [ Infix (do (token "->" <|> token "→") ; pure (EPi "_")) AssocLeft ]
        , [ Infix (do token ":"; pure EAnnot) AssocLeft]
        , [ Infix (do (token "===" <|> token "≡"); pure EEquivalent) AssocLeft]
        , [ Prefix (do token "assert"; token ":"; pure EAssert)]
        , [ Infix (do token "&&"; pure EBoolAnd) AssocLeft]
        , [ Infix (do token "#"; pure EListAppend) AssocLeft]]

mutual
  recordTypeElem : Parser (FieldName, Expr ImportStatement)
  recordTypeElem = do
    k <- identity
    token ":"
    e <- expr
    pure (MkFieldName k, e)

  recordTypeEmpty : Parser (Expr ImportStatement)
  recordTypeEmpty = do
    token "{"
    token "}"
    pure (ERecord (fromList []))

  recordTypeNonEmpty : Parser (Expr ImportStatement)
  recordTypeNonEmpty = do
    token "{"
    xs <- recordTypeElem `sepBy` (token ",")
    token "}"
    pure (ERecord (fromList xs))

  recordType : Parser (Expr ImportStatement)
  recordType = do
    recordTypeEmpty <|> recordTypeNonEmpty

  recordLitElem : Parser (FieldName, Expr ImportStatement)
  recordLitElem = do
    k <- identity
    token "="
    e <- expr
    pure (MkFieldName k, e)

  recordLitEmpty : Parser (Expr ImportStatement)
  recordLitEmpty = do
    token "{"
    token "="
    token "}"
    pure (ERecordLit (fromList []))

  recordLitNonEmpty : Parser (Expr ImportStatement)
  recordLitNonEmpty = do
    token "{"
    xs <- recordLitElem `sepBy` (token ",")
    token "}"
    pure (ERecordLit (fromList xs))

  recordLit : Parser (Expr ImportStatement)
  recordLit = do
    recordLitEmpty <|> recordLitNonEmpty

  unionSimpleElem : Parser (FieldName, Maybe (Expr ImportStatement))
  unionSimpleElem = do
    k <- identity
    pure (MkFieldName k, Nothing)

  unionComplexElem : Parser (FieldName, Maybe (Expr ImportStatement))
  unionComplexElem = do
    k <- identity
    token ":"
    e <- expr
    pure (MkFieldName k, Just e)

  unionElem : Parser (FieldName, Maybe (Expr ImportStatement))
  unionElem = unionComplexElem <|> unionSimpleElem

  union : Parser (Expr ImportStatement)
  union = do
    token "<"
    xs <- unionElem `sepBy` (token "|")
    token ">"
    pure (EUnion (fromList xs))

  -- TODO for multi-let the last let MUST have an `in`, the rest are optional.
  -- Need to parse this somehow.
  letExpr : Parser (Expr ImportStatement)
  letExpr = token "let" *> do
    i <- identity
    t <- optional (do token ":"; expr)
    token "="
    v <- expr
    spaces
    optional (token "in")
    e <- expr
    pure (ELet i t v e)

  piComplex : Parser (Expr ImportStatement)
  piComplex = do
    (token "forall(" <|> token "∀(")
    i <- identity
    token ":"
    dom <- expr
    spaces
    token ")"
    (token "->" <|> token "→")
    ran <- expr
    pure (EPi i dom ran)

  pi : Parser (Expr ImportStatement)
  pi = piComplex

  emptyList : Parser (Expr ImportStatement)
  emptyList = do
    token "["
    token "]"
    token ":"
    e <- expr
    pure (EListLit (Just e) [])

  populatedList : Parser (Expr ImportStatement)
  populatedList = do
    token "["
    es <- commaSep1 expr
    token "]"
    pure (EListLit Nothing es)

  annotatedList : Parser (Expr ImportStatement)
  annotatedList = do
    token "["
    es <- commaSep1 expr
    token "]"
    token ":"
    e <- expr
    pure (EListLit (Just e) es)

  list : Parser (Expr ImportStatement)
  list = emptyList <|> annotatedList <|> populatedList

  -- https://github.com/dhall-lang/dhall-haskell/blob/56bf1163a1331f72f7a55c06ab5ef77a60960630/dhall/src/Dhall/Syntax.hs#L1107
  -- https://github.com/dhall-lang/dhall-haskell/blob/56bf1163a1331f72f7a55c06ab5ef77a60960630/dhall/src/Dhall/Parser/Token.hs#L584
  dirCharacters : Parser Char
  dirCharacters = alphaNum <|> (char '.')

  dirs : Parser (List String)
  dirs = do
    dirs <- sepBy (some dirCharacters) (char '/') -- TODO handle spaces
    pure (map pack dirs)

  absolutePath : Parser Path
  absolutePath = do
    string "/"
    d <- dirs
    pure (Absolute d)

  homePath : Parser Path
  homePath = do
    string "~"
    d <- dirs
    pure (Home ("~" :: d))

  relPath : Parser Path
  relPath = do
    str <- ((string' "." <* char '/') <|> (string' ".." <* char '/'))
    d <- dirs
    pure (Relative (str :: d))

  pathTerm : Parser (Expr ImportStatement)
  pathTerm = do
    ex <- relPath <|> homePath <|> absolutePath
    pure (EEmbed (Raw (LocalFile (filePathFromPath ex))))

  lam : Parser (Expr ImportStatement)
  lam = do
    (string "λ(" <|> string "\\(")
    i <- identity
    token ":"
    ty <- expr
    spaces
    token ")"
    (token "->" <|> token "→")
    e <- expr
    pure (ELam i ty e)

  esome : Parser (Expr ImportStatement)
  esome = do
    token "Some"
    e <- expr
    pure (ESome e)

  term : Parser (Expr ImportStatement)
  term = do
    i <-(builtin <|>
     true <|> false <|> bool <|>
     double <|> doubleLit <|>
     natural <|> naturalLit <|>
     integer <|> integerLit <|>
     text <|> textLiteral <|>
     type <|> kind <|> sort <|>
     pathTerm <|> esome <|>
     recordType <|> recordLit <|>
     union <|>
     var <|> list <|> parens expr)
    spaces
    pure i

  interpolation : Parser (Chunks ImportStatement)
  interpolation = do
    string "${"
    e <- expr
    char '}'
    pure (MkChunks [(neutral, e)] neutral)

  unescapedCharacterFast : Parser (Chunks ImportStatement)
  unescapedCharacterFast = do x <- takeWhile1 predicate
                              pure (MkChunks [] x)
  where
    predicate : Char -> Bool
    predicate c = (  ('\x20' <= c && c <= '\x21')
                  || ('\x23' <= c && c <= '\x5B')
                  || ('\x5D' <= c && c <= '\x10FFFF')
                  ) && c /= '$'

  unescapedCharacterSlow : Parser (Chunks ImportStatement)
  unescapedCharacterSlow = do
                char '$'
                pure (MkChunks [] "$")

  escapedCharacter : Parser (Chunks ImportStatement)
  escapedCharacter =
            do  _ <- char '\\'
                c <- choice
                    (the (List (Parser Char))
                    [ char '"' -- quotationMark
                    , char '$' -- dollarSign
                    , char '\\' -- backslash
                    , char '/' -- forwardslash
                    , do char 'b'; pure '\b' -- backSpace
                    , do char 'f'; pure '\f' -- formFeed
                    , do char 'n'; pure '\n' -- lineFeed
                    , do char 'r'; pure '\r' -- carriageReturn
                    , do char 't'; pure '\t' -- tab
                    , unicode
                    ])
                pure (MkChunks [] (singleton c))

  doubleQuotedChunk : Parser (Chunks ImportStatement)
  doubleQuotedChunk = interpolation <|> unescapedCharacterFast <|> unescapedCharacterSlow <|> escapedCharacter

  doubleQuotedLiteral : Parser (Chunks ImportStatement)
  doubleQuotedLiteral = do
            char '"'
            chunks <- many doubleQuotedChunk
            char '"'
            pure (concat chunks)

  textLiteral : Parser (Expr ImportStatement)
  textLiteral = (do
            literal <- doubleQuotedLiteral
            pure (ETextLit literal) ) <?> "literal"

  opExpr : Parser (Expr ImportStatement)
  opExpr = buildExpressionParser (Expr ImportStatement) table term

  expr : Parser (Expr ImportStatement)
  expr = letExpr <|> pi <|> lam <|> opExpr <|> term

  parseToEnd : Parser (Expr ImportStatement)
  parseToEnd = do
    e <- expr
    eos
    pure e

public export
parseExpr : String -> Either String (Expr ImportStatement, Int)
parseExpr str = parse parseToEnd str
