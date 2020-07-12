import Lightyear.Combinators
import Lightyear.Core
import Lightyear.Char
import Lightyear.Strings

import Idrall.Expr
import Idrall.BuildExprParser
import Idrall.Path

fNaturalIsZero : (Expr ImportStatement)
fNaturalIsZero = ELam "naturalIsZeroParam1" ENatural (ENaturalIsZero (EVar "naturalIsZeroParam1"))

fList : (Expr ImportStatement)
fList = ELam "listArg1" (EConst CType) (EList (EVar "listArg1"))

%access export
builtin : Parser (Expr ImportStatement)
builtin =
  (string "Natural/isZero" *> pure fNaturalIsZero) <|>
  (string "List" *> pure fList)

true : Parser (Expr ImportStatement)
true = token "True" *> pure (EBoolLit True)

false : Parser (Expr ImportStatement)
false = token "False" *> pure (EBoolLit False)

bool : Parser (Expr ImportStatement)
bool = token "Bool" *> pure (EBool)

natural : Parser (Expr ImportStatement)
natural = token "Natural" *> pure (ENatural)

naturalLit : Parser (Expr ImportStatement)
naturalLit = do n <- some digit
                pure (ENaturalLit (getNatural n))
where getNatural : List (Fin 10) -> Nat
      getNatural = foldl (\a => \b => 10 * a + cast b) 0

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

identLong : Parser String
identLong = do f <- identFirst
               r <- some identRest -- TODO check for reservered words, back ticks
               pure (pack (f :: r))

identShort : Parser String
identShort = do i <- identFirst
                pure (singleton i)

reservedNames' : List String
reservedNames' =
  [ "in", "let", "assert"
  , "->", "&&", ":"
  , "List", "Optional", "Natural"
  , "Type", "Kind", "Sort"]

parseAny : List String -> Parser String
parseAny [] = string "provideListOfReservedNames" -- TODO find better version of this
parseAny (x :: xs) = string x <|> (parseAny xs)

reservedNames : Parser ()
reservedNames = do
  parseAny reservedNames'
  (do space; pure ()) <|> eof

identity : Parser String
identity = do
  _ <- requireFailure reservedNames
  (identLong <|> identShort) <* spaces

var : Parser (Expr ImportStatement)
var = do i <- identity
         pure (EVar i)

appl : Parser ((Expr ImportStatement) -> (Expr ImportStatement) -> (Expr ImportStatement))
appl = do spaces
          _ <- requireFailure reservedNames
          pure EApp

table : OperatorTable (Expr ImportStatement)
table = [ [ Infix appl AssocLeft]
        , [ Infix (do token ":"; pure EAnnot) AssocLeft]
        , [ Infix (do (token "===" <|> token "≡"); pure EEquivalent) AssocLeft]
        , [ Prefix (do token "assert"; token ":"; pure EAssert)]
        , [ Infix (do token "&&"; pure EBoolAnd) AssocLeft]
        , [ Infix (do token "#"; pure EListAppend) AssocLeft]]

mutual
  letExpr : Parser (Expr ImportStatement) -- TODO handle type annotation
  letExpr = token "let" *> do
    i <- identity
    spaces
    token "="
    v <- expr
    spaces
    token "in"
    e <- expr
    pure (ELet i Nothing v e)

  piSimple : Parser (Expr ImportStatement)
  piSimple = do
    dom <- term
    -- spaces
    (token "->" <|> token "→")
    ran <- expr
    pure (EPi "_" dom ran)

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
  pi = piComplex <|> piSimple

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

  dirCharacters : Parser String
  dirCharacters = do
    c <- alphaNum
    ?dirCharacters_rhs

  dirs : Parser (List String)
  dirs = do
    dirs <- sepBy (some (alphaNum <|> (char '.'))) (char '/') -- TODO handle spaces
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
    str <- ((string "." <* char '/') <|> (string ".." <* char '/'))
    d <- dirs
    pure (Relative (str :: d))

  pathTerm : Parser (Expr ImportStatement)
  pathTerm = do
    ex <- relPath <|> homePath <|> absolutePath
    pure (EEmbed (Raw (LocalFile ex)))

  lam : Parser (Expr ImportStatement)
  lam = do
    string "λ(" -- TODO <|> string "\\(")
    i <- identity
    token ":"
    ty <- expr
    spaces
    token ")"
    (token "->" <|> token "→")
    e <- expr
    pure (ELam i ty e)

  term : Parser (Expr ImportStatement)
  term = do
    i <-(builtin <|>
     true <|> false <|> bool <|>
     naturalLit <|> natural <|>
     type <|> kind <|> sort <|>
     pathTerm <|>
     var <|>| list <|>| parens expr)
    spaces
    pure i

  opExpr : Parser (Expr ImportStatement)
  opExpr = buildExpressionParser (Expr ImportStatement) table term

  expr : Parser (Expr ImportStatement)
  expr = letExpr <|> pi <|> lam <|> opExpr <|> term

  parseToEnd : Parser (Expr ImportStatement)
  parseToEnd = do
    e <- expr
    eof
    pure e

parseExpr : String -> Either String (Expr ImportStatement)
parseExpr str = parse parseToEnd str
