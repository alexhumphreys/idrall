import Lightyear.Combinators
import Lightyear.Core
import Lightyear.Char
import Lightyear.Strings

import Idrall.Expr
import Idrall.BuildExprParser

%access public export
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
value = true <|> false <|> bool <|>
        naturalLit <|> natural <|>
        type

expr : Parser Expr
expr = value

parseExpr : String -> Either String Expr
parseExpr str = parse expr str
