module Idrall.ParserNew

import Data.List
import Data.List1

import Text.Parser
import Text.Quantity
import Text.Token
import Text.Lexer
import Text.Bounded

import Idrall.Parser.Lexer

public export
FilePos : Type
FilePos = (Nat, Nat)

-- does fancy stuff for idris, for now it can just be a Maybe filename

OriginDesc : Type
OriginDesc = Maybe String

public export
data FC = MkFC        OriginDesc FilePos FilePos
        | ||| Virtual FCs are FC attached to desugared/generated code.
          MkVirtualFC OriginDesc FilePos FilePos
        | EmptyFC

Show FC where
  show (MkFC Nothing x y) = "\{show x}-\{show y}"
  show (MkFC (Just s) x y) = "\{s}:\{show x}-\{show y}"
  show (MkVirtualFC x y z) = "MkVirtualFCTODO"
  show EmptyFC = "(,)"

both : (a -> b) -> (a, a) -> (b, b)
both f x = (f (fst x), f (snd x))

boundToFC : OriginDesc -> WithBounds t -> FC
boundToFC mbModIdent b = MkFC mbModIdent (both cast $ start b) (both cast $ end b)

mergeBounds : FC -> FC -> FC
mergeBounds (MkFC x start _) (MkFC y _ end) = (MkFC x start end)
mergeBounds (MkFC x start _) (MkVirtualFC y _ end) = (MkFC x start end)
mergeBounds f@(MkFC x start end) EmptyFC = f
mergeBounds (MkVirtualFC x start _) (MkFC y _ end) = (MkFC y start end)
mergeBounds (MkVirtualFC x start _) (MkVirtualFC y _ end) = (MkVirtualFC x start end)
mergeBounds f@(MkVirtualFC x start end) EmptyFC = f
mergeBounds EmptyFC f@(MkFC x start end) = f
mergeBounds EmptyFC f@(MkVirtualFC x start end) = f
mergeBounds EmptyFC EmptyFC = EmptyFC

||| Raw AST representation generated directly from the parser
data Expr a
  = EVar FC String
  | EBoolLit FC Bool
  | EBoolAnd FC (Expr a) (Expr a)
  | ELet FC String (Expr a) (Expr a)
  | EList FC (List (Expr a))
  | EWith FC (Expr a) (List1 String) (Expr a)

Show (Expr a) where
  show (EVar fc x) = "(\{show fc}:EVar \{show x})"
  show (EBoolLit fc x) = "\{show fc}:EBoolLit \{show x}"
  show (EBoolAnd fc x y) = "(\{show fc}:EBoolAnd \{show x} \{show y})"
  show (ELet fc x y z) = "(\{show fc}:ELet \{show fc} \{show x} \{show y} \{show z})"
  show (EList fc x) = "(\{show fc}:EList \{show fc} \{show x})"
  show (EWith fc x s y) = "(\{show fc}:EWith \{show fc} \{show x} \{show s} \{show y})"

getBounds : Expr a -> FC
getBounds (EVar x _) = x
getBounds (EBoolLit x _) = x
getBounds (EBoolAnd x _ _) = x
getBounds (ELet x _ _ _) = x
getBounds (EList x _) = x
getBounds (EWith x _ _ _) = x

updateBounds : FC -> Expr a -> Expr a
updateBounds x (EVar _ z) = EVar x z
updateBounds x (EBoolLit _ z) = EBoolLit x z
updateBounds x (EBoolAnd _ z w) = EBoolAnd x z w
updateBounds x (ELet _ z w v) = ELet x z w v
updateBounds x (EList _ z) = EList x z
updateBounds x (EWith _ z s y) = EWith x z s y

chainr1 : Grammar state (TokenRawToken) True (a)
       -> Grammar state (TokenRawToken) True (a -> a -> a)
       -> Grammar state (TokenRawToken) True (a)
chainr1 p op = p >>= rest
where
  rest : a -> Grammar state (TokenRawToken) False (a)
  rest a1 = (do f <- op
                a2 <- p >>= rest
                rest (f a1 a2)) <|> pure a1

chainl1 : Grammar state (TokenRawToken) True (a)
       -> Grammar state (TokenRawToken) True (a -> a -> a)
       -> Grammar state (TokenRawToken) True (a)
chainl1 p op = do
  x <- p
  rest x
where
  rest : a -> Grammar state (TokenRawToken) False (a)
  rest a1 = (do
    f <- op
    a2 <- p
    rest (f a1 a2)) <|> pure a1

infixOp : Grammar state (TokenRawToken) True ()
        -> (a -> a -> a)
        -> Grammar state (TokenRawToken) True (a -> a -> a)
infixOp l ctor = do
  l
  Text.Parser.Core.pure ctor

boundedOp : (FC -> Expr a -> Expr a -> Expr a)
          -> Expr a
          -> Expr a
          -> Expr a
boundedOp op x y =
  let xB = getBounds x
      yB = getBounds y
      mB = mergeBounds xB yB in
      op mB x y

tokenW : Grammar state (TokenRawToken) True a -> Grammar state (TokenRawToken) True a
tokenW p = do
  x <- p
  _ <- optional $ match $ White
  pure x

mutual
  dottedList : Grammar state (TokenRawToken) True (List1 String)
  dottedList = do
    x <- sepBy1 (match $ Symbol ".") (match Ident)
    match $ White
    pure x

  builtinTerm : WithBounds (TokType Ident) -> Grammar state (TokenRawToken) False (Expr ())
  builtinTerm _ = fail "TODO not implemented"

  boolTerm : WithBounds (TokType Ident) -> Grammar state (TokenRawToken) False (Expr ())
  boolTerm b@(MkBounded "True" isIrrelevant bounds) = pure $ EBoolLit (boundToFC Nothing b) True
  boolTerm b@(MkBounded "False" isIrrelevant bounds) = pure $ EBoolLit (boundToFC Nothing b) False
  boolTerm (MkBounded _ isIrrelevant bounds) = fail "unrecognised const"

  varTerm : Grammar state (TokenRawToken) True (Expr ())
  varTerm = do
      name <- bounds $ match Ident
      _ <- optional $ match White
      builtinTerm name <|> boolTerm name <|> toVar (isKeyword name)
  where
    isKeyword : WithBounds (TokType Ident) -> Maybe $ Expr ()
    isKeyword b@(MkBounded val isIrrelevant bounds) =
      let isKeyword = elem val keywords
      in case (isKeyword) of
              (True) => Nothing
              (False) => pure $ EVar (boundToFC Nothing b) val
    toVar : Maybe $ Expr () -> Grammar state (TokenRawToken) False (Expr ())
    toVar Nothing = fail "is reserved word"
    toVar (Just x) = pure x

  letBinding : Grammar state (TokenRawToken) True (Expr ())
  letBinding = do
    start <- bounds $ tokenW $ match $ Keyword "let"
    name <- tokenW $ match $ Ident
    tokenW $ match $ Symbol "="
    e <- exprTerm
    match $ White
    end <- bounds $ tokenW $ match $ Keyword "in" -- TODO is this a good end position?
    e' <- exprTerm
    pure $ ELet (mergeBounds (boundToFC Nothing start) (boundToFC Nothing end)) name e e'

  atom : Grammar state (TokenRawToken) True (Expr ())
  atom = varTerm <|> listExpr <|> (between (match $ Symbol "(") (match $ Symbol ")") exprTerm)

  listExpr : Grammar state (TokenRawToken) True (Expr ())
  listExpr = emptyList <|> populatedList
  where
    emptyList : Grammar state (TokenRawToken) True (Expr ())
    emptyList = do
      start <- bounds $ match $ Symbol "["
      end <- bounds $ match $ Symbol "]"
      pure $ EList (mergeBounds (boundToFC Nothing start) (boundToFC Nothing end)) []
    populatedList : Grammar state (TokenRawToken) True (Expr ())
    populatedList = do
      start <- bounds $ match $ Symbol "["
      es <- sepBy1 (match $ Symbol ",") exprTerm
      end <- bounds $ match $ Symbol "]"
      pure $ EList (mergeBounds (boundToFC Nothing start) (boundToFC Nothing end)) (forget es)

  boolOp : FC -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
  boolOp fc = infixOp (tokenW $ match $ Symbol "&&") (boundedOp EBoolAnd)

  withOp : FC -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
  withOp fc =
    let foo = the (List1 String) ("foo":::[]) in
    do
      tokenW $ match $ Keyword "with"
      dl <- dottedList
      pure (boundedOp (with' dl))
  where
    with' : List1 String -> FC -> Expr a -> Expr a -> Expr a
    with' xs fc x y = EWith fc x xs y

  withTerm : Grammar state (TokenRawToken) True (Expr ())
  withTerm = chainl1 atom (go EmptyFC)
  where
    with' : List1 String -> FC -> Expr a -> Expr a -> Expr a
    with' xs fc x y = EWith fc x xs y
    go : FC -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
    go fc =
      let foo = the (List1 String) ("foo":::[]) in
      do
        tokenW $ match $ Keyword "with"
        dl <- dottedList
        pure (boundedOp (with' dl))
        -- TODO how to pass `dl` instead of `foo`

  boolTerm' : Grammar state (TokenRawToken) True (Expr ())
  boolTerm' = chainl1 atom (boolOp EmptyFC)

  exprTerm : Grammar state (TokenRawToken) True (Expr ())
  exprTerm = do
    letBinding <|>
    chainl1 boolTerm' (withOp EmptyFC)

Show (Bounds) where
  show (MkBounds startLine startCol endLine endCol) =
    "sl:\{show startLine} sc:\{show startCol} el:\{show endLine} ec:\{show endCol}"

Show (ParsingError (TokenRawToken)) where
  show (Error x xs) =
    """
    error: \{x}
    tokens: \{show xs}
    """

doParse : String -> IO ()
doParse input = do
  let tokens = lexRaw input
  putStrLn $ "tokens: " ++ show tokens

  Right (expr, x) <- pure $ parse exprTerm tokens
    | Left e => printLn $ show e
  putStrLn $
    """
    expr: \{show expr}
    x: \{show x}
    """
