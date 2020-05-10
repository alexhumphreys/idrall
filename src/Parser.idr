Parser : Type -> Type
Parser a = String -> List (a, String)

result : a -> Parser a
result v = \inp => [(v,inp)]

zero : Parser a
zero = \inp => []

item : Parser Char
item = \inp => case inp of
                    [] => []
                    (x::xs) => [(x,xs)]

bind : Parser a -> (a -> Parser b) -> Parser b
bind p f = \inp => concat [f v inp' | (v,inp') <- p inp]

sat : (Char -> Bool) -> Parser Char
sat p = bind item (\x => if p x then result x else zero)
