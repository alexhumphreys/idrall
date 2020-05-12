import Lightyear.Combinators
import Lightyear.Core
import Lightyear.Char
import Lightyear.Strings

import Idrall.Expr
import Idrall.BuildExprParser

%access public export
true : Parser Expr
true = token "True" *> pure (EBoolLit True)

bool : Parser Expr
bool = token "Bool" *> pure (EBool)

type : Parser Expr
type = token "Type" *> pure (EConst CType)

expr : Parser Expr
expr = true <|> type

parseExpr : String -> Either String Expr
parseExpr str = parse expr str
