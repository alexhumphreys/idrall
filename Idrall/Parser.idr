module Idrall.Parser

import Control.Monad.Identity
import Control.Monad.Trans

import Data.Fin
import Data.Nat
import Data.String
import Data.List1
import Data.String.Parser
import Data.String.Parser.Expression

import Idrall.Lexer
import Idrall.Expr
import Idrall.Path

%hide Prelude.pow

initFC : FC
initFC = EmptyFC

builtin : Parser (Expr ImportStatement)
builtin =
  (string "Natural/build" *> pure (ENaturalBuild initFC)) <|>
  (string "Natural/fold" *> pure (ENaturalFold initFC)) <|>
  (string "Natural/isZero" *> pure (ENaturalIsZero initFC)) <|>
  (string "Natural/even" *> pure (ENaturalEven initFC)) <|>
  (string "Natural/odd" *> pure (ENaturalOdd initFC)) <|>
  (string "Natural/subtract" *> pure (ENaturalSubtract initFC)) <|>
  (string "Natural/toInteger" *> pure (ENaturalToInteger initFC)) <|>
  (string "Natural/show" *> pure (ENaturalShow initFC)) <|>
  (string "Integer/show" *> pure (EIntegerShow initFC)) <|>
  (string "Integer/negate" *> pure (EIntegerNegate initFC)) <|>
  (string "Integer/clamp" *> pure (EIntegerClamp initFC)) <|>
  (string "Integer/toDouble" *> pure (EIntegerToDouble initFC)) <|>
  (string "Double/show" *> pure (EDoubleShow initFC)) <|>
  (string "List/build" *> pure (EListBuild initFC)) <|>
  (string "List/fold" *> pure (EListFold initFC)) <|>
  (string "List/length" *> pure (EListLength initFC)) <|>
  (string "List/head" *> pure (EListHead initFC)) <|>
  (string "List/last" *> pure (EListLast initFC)) <|>
  (string "List/indexed" *> pure (EListIndexed initFC)) <|>
  (string "List/reverse" *> pure (EListReverse initFC)) <|>
  (string "List" *> pure (EList initFC)) <|>
  (string "Text/show" *> pure (ETextShow initFC)) <|>
  (string "Text/replace" *> pure (ETextReplace initFC)) <|>
  (string "None" *> pure (ENone initFC)) <|>
  (string "Optional" *> pure (EOptional initFC)) <|>
  (string "NaN" *> pure (EDoubleLit initFC (0.0/0.0)))

true : Parser (Expr ImportStatement)
true = string "True" *> pure (EBoolLit initFC True)

false : Parser (Expr ImportStatement)
false = string "False" *> pure (EBoolLit initFC False)

bool : Parser (Expr ImportStatement)
bool = string "Bool" *> pure (EBool initFC)

text : Parser (Expr ImportStatement)
text = string "Text" *> pure (EText initFC)

integer : Parser (Expr ImportStatement)
integer = string "Integer" *> pure (EInteger initFC)

integerLit : Parser (Expr ImportStatement)
integerLit = do op <- (char '-' <|> char '+')
                x <- some digit
                case op of
                     '+' => pure (EIntegerLit initFC (getInteger x))
                     '-' => pure (EIntegerLit initFC ((getInteger x)*(-1)))
                     _ => fail "not an Integer"
where getInteger : List (Fin 10) -> Integer
      getInteger = foldl (\a => \b => 10 * a + cast b) 0

natural : Parser (Expr ImportStatement)
natural = string "Natural" *> pure (ENatural initFC)

double : Parser (Expr ImportStatement)
double = string "Double" *> pure (EDouble initFC)

naturalNumber : Parser Nat
naturalNumber = do n <- some digit
                   pure $ getNatural n
where getNatural : List (Fin 10) -> Nat
      getNatural = foldl (\a => \b => 10 * a + cast b) 0

naturalLit : Parser (Expr ImportStatement)
naturalLit = do n <- naturalNumber
                pure (ENaturalLit initFC n)

-- From lightyear JSON parser
record Scientific where
  constructor MkScientific
  coefficient : Integer
  exponent : Integer

scientificToDouble : Scientific -> Double
scientificToDouble (MkScientific c e) =
  let c' = fromInteger c in
    if e < 0 then c' / pow' 10 (fromInteger (- e))
             else c' * pow' 10 (fromInteger e)
  where
    pow' : (Num a) => a -> Nat -> a
    pow' x Z = 1
    pow' x (S n) = x * (pow' x n)

data Sign
  = PlusSign
  | MinusSign

signToInt : Maybe Sign -> Integer
signToInt (Just MinusSign) = -1
signToInt _ = 1

parseSign : Parser Sign
parseSign = char '-' *> pure MinusSign <|> char '+' *> pure PlusSign

parseScientific : Parser Scientific
parseScientific = do sign <- optional parseSign
                     digits <- some digit
                     hasDecimals <- isJust `map` optional (char '.')
                     decimals <- if hasDecimals then some digit else pure []
                     hasExponent <- isJust `map` optional (char 'e')
                     exponent <- if hasExponent then integer else pure 0
                     guard (hasExponent || hasDecimals)
                     pure $ MkScientific ((signToInt sign) * fromDigits (digits ++ decimals))
                                         (exponent - cast (length decimals))
  where fromDigits : List (Fin 10) -> Integer
        fromDigits = foldl (\a, b => 10 * a + cast b) 0

doubleLit : Parser (Expr ImportStatement)
doubleLit = do k <- map scientificToDouble parseScientific
               pure (EDoubleLit initFC k)

type : Parser (Expr ImportStatement)
type = token "Type" *> pure (EConst initFC CType)

kind : Parser (Expr ImportStatement)
kind = token "Kind" *> pure (EConst initFC Kind)

sort : Parser (Expr ImportStatement)
sort = token "Sort" *> pure (EConst initFC Sort)

identFirst : Parser Char
identFirst = letter <|> char '_'

identRest : Parser Char
identRest = alphaNum <|> char '-' <|> char '/' <|> char '_'

identLong : Parser String
identLong = do f <- identFirst
               r <- some identRest
               pure (pack (f :: r))

identShort : Parser String
identShort = do i <- identFirst
                pure (singleton i)

reservedKeywords : List String
reservedKeywords =
  [ "if", "then", "else"
  , "let", "in"
  , "using", "missing"
  , "assert", "as"
  , "Infinity", "NaN"
  , "merge", "toMap"
  , "forall"
  , "with"
  ]

reservedBuiltin : List String
reservedBuiltin =
  [ "Natural/fold"
  , "Natural/build"
  , "Natural/isZero"
  , "Natural/even"
  , "Natural/odd"
  , "Natural/toInteger"
  , "Natural/show"
  , "Integer/toDouble"
  , "Integer/show"
  , "Integer/negate"
  , "Integer/clamp"
  , "Natural/subtract"
  , "Double/show"
  , "List/build"
  , "List/fold"
  , "List/length"
  , "List/head"
  , "List/last"
  , "List/indexed"
  , "List/reverse"
  , "Text/show"
  , "Text/replace"
  , "Bool"
  , "True"
  , "False"
  , "Optional"
  , "None"
  , "Natural"
  , "Integer"
  , "Double"
  , "Text"
  , "List"
  , "Type"
  , "Kind"
  , "Sort"
  ]

reservedSome : List String
reservedSome = ["Some"]

parseAny : List String -> Parser ()
parseAny [] = fail "emptyList" -- TODO use List1 in idris2 to remove this case
parseAny (x :: xs) = skip (string x) <|> (parseAny xs)

identity : Parser String
identity = do i <- (identLong <|> identShort)
              case elem i (reservedBuiltin ++ reservedKeywords ++ reservedSome) of
                   True => fail $ show i ++ " is reserved"
                   False => pure i

fieldName' : Parser String
fieldName' = do
  i <- (identLong <|> identShort)
  case elem i reservedKeywords of
       True => fail $ show i ++ " is reserved"
       False => pure i

backticked : Parser String
backticked = do
  _ <- char '`'
  rest <- takeWhile1 (\c => c /= '`')
  _ <- char '`'
  pure rest

varBackticks : Parser (Expr ImportStatement)
varBackticks = do
  i <- backticked
  pure $ EVar initFC i 0

varRegular : Parser (Expr ImportStatement)
varRegular = do i <- identity
                pure (EVar initFC i 0)

varIndexed : Parser (Expr ImportStatement)
varIndexed = do i <- identity
                whitespace
                token "@"
                n <- naturalNumber
                pure (EVar initFC i (cast n))

var : Parser (Expr ImportStatement)
var = varBackticks <|> varIndexed <|> varRegular

fieldName : Parser String
fieldName = backticked <|> fieldName'

identityDefinition : Parser String
identityDefinition = identity <|> backticked

appl : Parser ((Expr ImportStatement) -> (Expr ImportStatement) -> (Expr ImportStatement))
appl = do whitespace -- TODO also matches no spaces, but spaces1 messes with the eos parser
          pure $ EApp initFC

projectNames : Parser ((Expr ImportStatement) -> (Expr ImportStatement))
projectNames = do
  token ".{"
  xs <- (fieldName <* spaces) `sepBy` (token ",")
  token "}"
  pure (\e => (EProject initFC e (Left (map MkFieldName xs))))

dottedList : Parser (List1 FieldName)
dottedList = do
  ks <- (fieldName <* spaces) `sepBy1` (token ".")
  pure $ (map MkFieldName ks)

field : Parser ((Expr ImportStatement) -> (Expr ImportStatement))
field = do
  token "."
  ks <- dottedList
  pure $ (\e' => foldl (EField initFC) (EField initFC e' (head ks)) (tail ks))

mutual
  projectByType : Parser ((Expr ImportStatement) -> (Expr ImportStatement))
  projectByType = do
    token ".("
    e <- expr
    token ")"
    pure (\e' => (EProject initFC e' (Right e)))

  -- TODO with is currently right associative and should be left
  withExpr : Parser ((Expr ImportStatement) -> (Expr ImportStatement))
  withExpr = do
    token "with"
    ks <- dottedList
    token "="
    e <- expr
    pure (\e' => (EWith initFC e' ks e))

  table : OperatorTable (Expr ImportStatement)
  table = [ [ Postfix projectNames
            , Postfix projectByType
            , Postfix field
            , Infix appl AssocLeft
            , Postfix withExpr
            ]
          , [ Infix (do (token "->" <|> token "→") ; pure (EPi initFC "_")) AssocRight ]
          , [ Infix (do token ":"; pure (EAnnot initFC)) AssocLeft]
          , [ Infix (token "&&" $> EBoolAnd initFC) AssocLeft
            , Infix (token "||" $> EBoolOr initFC) AssocLeft
            , Infix (token "==" $> EBoolEQ initFC) AssocLeft
            , Infix (token "!=" $> EBoolNE initFC) AssocLeft
            , Infix (token "*" $> ENaturalTimes initFC) AssocLeft
            , Infix (token "++" $> ETextAppend initFC) AssocLeft
            ]
          , [ Infix (token "+" $> ENaturalPlus initFC) AssocLeft]
          , [ Infix (do (token "===" <|> token "≡"); pure (EEquivalent initFC)) AssocLeft]
          , [ Prefix (do token "assert"; token ":"; pure (EAssert initFC))]
          , [ Infix (do token "#"; pure (EListAppend initFC)) AssocLeft]
          , [ Infix (pure (ECombine initFC) <* (token "/\\" <|> token "∧")) AssocLeft
            , Infix (pure (EPrefer initFC) <* (token "//" <|> token "⫽")) AssocLeft
            , Infix (pure (ECombineTypes initFC) <* (token "//\\\\" <|> token "⩓")) AssocLeft
            , Infix (pure (ERecordCompletion initFC) <* (token "::")) AssocLeft
            , Infix (pure (EImportAlt initFC) <* (token "?")) AssocLeft
            ]
          ]

  recordTypeElem : Parser (FieldName, Expr ImportStatement)
  recordTypeElem = do
    k <- fieldName
    whitespace
    token ":"
    e <- expr
    pure (MkFieldName k, e)

  recordTypeEmpty : Parser (Expr ImportStatement)
  recordTypeEmpty = do
    token "{"
    token "}"
    pure (ERecord initFC (fromList []))

  recordTypeNonEmpty : Parser (Expr ImportStatement)
  recordTypeNonEmpty = do
    token "{"
    xs <- recordTypeElem `sepBy` (token ",")
    token "}"
    pure (ERecord initFC (fromList xs))

  recordType : Parser (Expr ImportStatement)
  recordType = do
    recordTypeEmpty <|> recordTypeNonEmpty

  recordLitRegularElem : Parser (SortedMap FieldName (Expr ImportStatement))
  recordLitRegularElem = do
    k <- fieldName
    whitespace
    token "="
    e <- expr
    pure $ fromList [(MkFieldName k, e)]

  recordLitPunElem : Parser (SortedMap FieldName (Expr ImportStatement))
  recordLitPunElem = do
    k <- fieldName
    whitespace
    pure $ fromList [(MkFieldName k, (EVar initFC k 0))]

  recordLitDottedElem : Parser (SortedMap FieldName (Expr ImportStatement))
  recordLitDottedElem = do
    ks <- dottedList
    token "="
    e <- expr
    pure $ mkNestedRecord ks e
  where
    mkNestedRecord : List1 FieldName -> Expr ImportStatement -> SortedMap FieldName (Expr ImportStatement)
    mkNestedRecord ks e =
      let (k ::: ks') = reverse ks in
      foldl (\ms,k' => fromList [(k', ERecordLit initFC ms)]) (fromList [(k, e)]) ks'

  recordLitElem : Parser (SortedMap FieldName (Expr ImportStatement))
  recordLitElem = recordLitDottedElem <|> recordLitRegularElem <|> recordLitPunElem

  recordLitEmpty : Parser (Expr ImportStatement)
  recordLitEmpty = do
    token "{"
    token "="
    token "}"
    pure (ERecordLit initFC (fromList []))

  recordLitNonEmpty : Parser (Expr ImportStatement)
  recordLitNonEmpty = do
    token "{"
    (x ::: xs) <- recordLitElem `sepBy1` (token ",")
    token "}"
    pure $ ERecordLit initFC $ foldl (mergeWith (ECombine initFC)) x xs

  recordLit : Parser (Expr ImportStatement)
  recordLit = do
    recordLitEmpty <|> recordLitNonEmpty

  unionSimpleElem : Parser (FieldName, Maybe (Expr ImportStatement))
  unionSimpleElem = do
    k <- fieldName
    whitespace
    pure (MkFieldName k, Nothing)

  unionComplexElem : Parser (FieldName, Maybe (Expr ImportStatement))
  unionComplexElem = do
    k <- fieldName
    whitespace
    token ":"
    e <- expr
    pure (MkFieldName k, Just e)

  unionElem : Parser (FieldName, Maybe (Expr ImportStatement))
  unionElem = unionComplexElem <|> unionSimpleElem

  union : Parser (Expr ImportStatement)
  union = do
    token "<"
    xs <- unionElem `sepBy` (token "|")
    whitespace
    token ">"
    pure (EUnion initFC (fromList xs))

  -- TODO for multi-let the last let MUST have an `in`, the rest are optional.
  -- Need to parse this somehow.
  letExpr : Parser (Expr ImportStatement)
  letExpr = do
    token "let"
    _ <- optional whitespace
    i <- identityDefinition
    spaces
    t <- optional (do token ":"; expr)
    token "="
    v <- expr
    whitespace
    _ <- optional (token "in")
    e <- expr
    pure (ELet initFC i t v e)

  piComplex : Parser (Expr ImportStatement)
  piComplex = do
    (token "forall(" <|> (token "∀" *> token "("))
    i <- identityDefinition
    _ <- optional whitespace
    token ":"
    dom <- expr
    _ <- optional whitespace
    token ")"
    (token "->" <|> token "→")
    ran <- expr
    pure (EPi initFC i dom ran)

  pi : Parser (Expr ImportStatement)
  pi = piComplex

  ifExpr : Parser (Expr ImportStatement)
  ifExpr = do
    token "if"
    x <- expr
    token "then"
    y <- expr
    token "else"
    z <- expr
    pure (EBoolIf initFC x y z)

  emptyList : Parser (Expr ImportStatement)
  emptyList = do
    token "["
    token "]"
    token ":"
    e <- expr
    pure (EListLit initFC (Just e) [])

  populatedList : Parser (Expr ImportStatement)
  populatedList = do
    token "["
    es <- commaSep1' expr
    token "]"
    pure (EListLit initFC Nothing (forget es))

  annotatedList : Parser (Expr ImportStatement)
  annotatedList = do
    token "["
    es <- commaSep1' expr
    token "]"
    token ":"
    e <- expr
    pure (EListLit initFC (Just e) (forget es))

  list : Parser (Expr ImportStatement)
  list = emptyList <|> annotatedList <|> populatedList

  -- https://github.com/dhall-lang/dhall-haskell/blob/56bf1163a1331f72f7a55c06ab5ef77a60960630/dhall/src/Dhall/Syntax.hs#L1107
  -- https://github.com/dhall-lang/dhall-haskell/blob/56bf1163a1331f72f7a55c06ab5ef77a60960630/dhall/src/Dhall/Parser/Token.hs#L584
  dirCharacters : Parser Char
  dirCharacters = alphaNum <|> (char '@') <|> (char '_') <|> (char '-') <|> (char '.')

  dirs : Parser (List String)
  dirs = do
    dirs <- sepBy (some dirCharacters) (char '/') -- TODO handle spaces
    pure (map pack dirs)

  absolutePath : Parser Path
  absolutePath = do
    requireFailure $ string "//"
    _ <- string "/"
    d <- dirs
    pure (Absolute d)

  homePath : Parser Path
  homePath = do
    _ <- string "~"
    d <- dirs
    pure (Home ("~" :: d))

  relPath : Parser Path
  relPath = do
    str <- ((string "." <* char '/') <|> (string ".." <* char '/'))
    d <- dirs
    pure (Relative (str :: d))

  pathTerm : Parser (ImportStatement)
  pathTerm = do
    ex <- relPath <|> homePath <|> absolutePath
    pure $ LocalFile (filePathFromPath ex)

  sha : Parser String
  sha = do
    token "sha256:"
    x <- many alphaNum
    pure $ pack x

  envVar : Parser (ImportStatement)
  envVar = do
    token "env:"
    x <- many (alphaNum <|> char '_')
    pure $ EnvVar $ pack x

  data Protocol = HTTP | HTTPS
  Show Protocol where
    show HTTP = "http://"
    show HTTPS = "https://"

  missingImport : Parser (ImportStatement)
  missingImport = do
    _ <- string "missing"
    pure $ Missing

  httpImport : Parser (ImportStatement)
  httpImport = do
    protocol <- token "http://" <|> token "https://"
    rest <- takeWhile (\c => c /= ' ')
    pure $ Http (show protocol ++ rest)

  dhallImportStatement : Parser (ImportStatement)
  dhallImportStatement = httpImport <|> pathTerm <|> envVar <|> missingImport

  importAs : Parser (a -> Import a)
  importAs = (token "Text" *> pure Text) <|> (token "Location" *> pure Location)

  basicImport : Parser (Expr ImportStatement)
  basicImport = do
    i <- dhallImportStatement
    pure (EEmbed initFC $ Raw i)

  shaImport : Parser (Expr ImportStatement)
  shaImport = do
    i <- dhallImportStatement
    spaces
    sha <- sha
    pure (EEmbed initFC $ Raw i)

  asImport : Parser (Expr ImportStatement)
  asImport = do
    i <- dhallImportStatement
    spaces
    token "as"
    asType <- importAs
    pure (EEmbed initFC (asType i))

  shaAndAsImport : Parser (Expr ImportStatement)
  shaAndAsImport = do
    i <- dhallImportStatement
    spaces
    sha <- optional sha
    spaces
    token "as"
    asType <- importAs
    pure (EEmbed initFC (asType i))

  dhallImport : Parser (Expr ImportStatement)
  dhallImport = shaAndAsImport <|> asImport <|> shaImport <|> basicImport

  lam : Parser (Expr ImportStatement)
  lam = do
    token "λ" <|> token "\\"
    token "("
    i <- identityDefinition
    whitespace
    token ":"
    ty <- expr
    whitespace
    token ")"
    (token "->" <|> token "→")
    e <- expr
    pure (ELam initFC i ty e)

  esome : Parser (Expr ImportStatement)
  esome = do
    token "Some"
    e <- expr
    pure (ESome initFC e)

  mergeExpr : Parser (Expr ImportStatement)
  mergeExpr = do
    token "merge"
    x <- expr
    case x of -- TODO hacky
         (EApp fc y z) => pure (EMerge fc y z Nothing)
         (EAnnot fc (EApp _ y z) t) => pure (EMerge fc y z (Just t))
         _ => do whitespace
                 y <- expr
                 whitespace
                 t <- optional (token ":" *> term)
                 case y of
                      (EAnnot fc y' a) => pure (EMerge fc x y' (Just a))
                      _ => pure (EMerge initFC x y t)

  toMap : Parser (Expr ImportStatement)
  toMap = do
    token "toMap"
    x <- expr
    case x of -- TODO hacky
         (EAnnot fc x y) => pure (EToMap fc x (Just y))
         x => pure (EToMap initFC x Nothing)

  term : Parser (Expr ImportStatement)
  term = do
    i <-(dhallImport <|>
     doubleLit <|>
     naturalLit <|>
     var <|> builtin <|> mergeExpr <|> toMap <|>
     true <|> false <|> bool <|> ifExpr <|>
     natural <|> double <|>
     integer <|> integerLit <|>
     text <|> textLiteral <|>
     type <|> kind <|> sort <|>
     esome <|>
     recordType <|> recordLit <|>
     union <|> lam <|> pi <|>
     list <|> parens (whitespace *> expr))
    whitespace
    pure i

  interpolation : Parser (Chunks ImportStatement)
  interpolation = do
    _ <- string "${"
    e <- expr
    _ <- char '}'
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
                _ <- char '$'
                pure (MkChunks [] "$")

  escapedCharacter : Parser (Chunks ImportStatement)
  escapedCharacter =
            do  _ <- char '\\'
                c <- choice
                    (the (List $ Lazy (Parser Char))
                    [ char '"' -- quotationMark
                    , char '$' -- dollarSign
                    , char '\\' -- backslash
                    , char '/' -- forwardslash
                    , do _ <- char 'b'; pure '\b' -- backSpace
                    , do _ <- char 'f'; pure '\f' -- formFeed
                    , do _ <- char 'n'; pure '\n' -- lineFeed
                    , do _ <- char 'r'; pure '\r' -- carriageReturn
                    , do _ <- char 't'; pure '\t' -- tab
                    , unicode
                    ])
                pure (MkChunks [] (singleton c))

  doubleQuotedChunk : Parser (Chunks ImportStatement)
  doubleQuotedChunk = interpolation <|> unescapedCharacterFast <|> unescapedCharacterSlow <|> escapedCharacter

  doubleQuotedLiteral : Parser (Chunks ImportStatement)
  doubleQuotedLiteral = do
            _ <- char '"'
            chunks <- many doubleQuotedChunk
            _ <- char '"'
            pure (concat chunks)

  singleQuoteContinue : Parser (Chunks ImportStatement)
  singleQuoteContinue =
    choice
      [ escapeSingleQuotes
      , interpolation
      , escapeInterpolation
      , endLiteral
      , unescapedCharacterFast
      , unescapedCharacterSlow
      , tab
      , endOfLine
      ]
  where
    escapeSingleQuotes : Parser (Chunks ImportStatement)
    escapeSingleQuotes = do
      _ <- string "'''"
      b <- singleQuoteContinue
      pure $ (MkChunks [] "''") <+> b
    interpolation : Parser (Chunks ImportStatement)
    interpolation = do
      _ <- string "${"
      a <- expr
      _ <- char '}'
      b <- singleQuoteContinue
      pure (MkChunks [(neutral, a)] neutral <+> b)
    escapeInterpolation : Parser (Chunks ImportStatement)
    escapeInterpolation = do
      _ <- string "''${"
      b <- singleQuoteContinue
      pure $ (MkChunks [] "${") <+> b
    endLiteral : Parser (Chunks ImportStatement)
    endLiteral = do
      _ <- string "''"
      pure neutral
    unescapedCharacterFast : Parser (Chunks ImportStatement)
    unescapedCharacterFast = do
      a <- takeWhile1 predicate
      b <- singleQuoteContinue
      pure (MkChunks [] a <+> b)
    where
      predicate : Char -> Bool
      predicate c =
          ('\x20' <= c && c <= '\x10FFFF') && c /= '$' && c /= '\''
    unescapedCharacterSlow : Parser (Chunks ImportStatement)
    unescapedCharacterSlow = do
      a <- satisfy predicate
      b <- singleQuoteContinue
      pure (MkChunks [] (singleton a) <+> b)
    where
      predicate : Char -> Bool
      predicate c = c == '$' || c == '\''
    endOfLine : Parser (Chunks ImportStatement)
    endOfLine = do
      a <- string "\n" <|> string "\r\n"
      b <- singleQuoteContinue
      pure (MkChunks [] a <+> b)
    tab : Parser (Chunks ImportStatement)
    tab = do
      _ <- char '\t' <?> "tab"
      b <- singleQuoteContinue
      pure (MkChunks [] "\t" <+> b)

  singleQuoteLiteral : Parser (Chunks ImportStatement)
  singleQuoteLiteral = do
    _ <- string "''"
    _ <- endOfLine
    a <- singleQuoteContinue
    pure a -- TODO handle indentation
  where
    endOfLine : Parser ()
    endOfLine = (skip (char '\n') <|> skip (string "\r\n")) <?> "newline"

  textLiteral : Parser (Expr ImportStatement)
  textLiteral = (do
            literal <- doubleQuotedLiteral <|> singleQuoteLiteral
            pure (ETextLit initFC literal) ) <?> "literal"

  opExpr : Parser (Expr ImportStatement)
  opExpr = buildExpressionParser (Expr ImportStatement) table term

  expr : Parser (Expr ImportStatement)
  expr = letExpr <|> pi <|> lam <|> opExpr <|> term

  parseToEnd : Parser (Expr ImportStatement)
  parseToEnd = do
    whitespace
    e <- expr
    eos
    pure e

public export
parseExpr : String -> Either String (Expr ImportStatement, Int)
parseExpr str = parse parseToEnd str
