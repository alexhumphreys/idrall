import Lightyear.Combinators
import Lightyear.Core
import Lightyear.Char
import Lightyear.Strings

import Idrall.Expr
import Idrall.BuildExprParser

fNaturalIsZero : Expr
fNaturalIsZero = ELam "naturalIsZeroParam1" ENatural (ENaturalIsZero (EVar "naturalIsZeroParam1"))

%access export
builtin : Parser Expr
builtin = string "Natural/isZero" *> pure fNaturalIsZero

true : Parser Expr
true = token "True" *> pure (EBoolLit True)

false : Parser Expr
false = token "False" *> pure (EBoolLit False)

bool : Parser Expr
bool = token "Bool" *> pure (EBool)

natural : Parser Expr
natural = token "Natural" *> pure (ENatural)

naturalLit : Parser Expr
naturalLit = do n <- some digit
                pure (ENaturalLit (getNatural n))
where getNatural : List (Fin 10) -> Nat
      getNatural = foldl (\a => \b => 10 * a + cast b) 0

type : Parser Expr
type = token "Type" *> pure (EConst CType)

value : Parser Expr
value = builtin <|>
        true <|> false <|> bool <|>
        naturalLit <|> natural <|>
        type

expr : Parser Expr
expr = value

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

identity : Parser String
identity = identLong <|> identShort

letExpr : Parser Expr -- TODO handle type annotation
letExpr = token "let" *> do
  i <- identity
  spaces
  token "="
  v <- expr
  spaces
  token "in"
  e <- expr
  pure (ELet i Nothing v e)

parseExpr : String -> Either String Expr
parseExpr str = parse expr str
