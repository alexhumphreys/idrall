module Idrall.ParserNew

import Data.List
import Data.List1

import Text.Parser
import Text.Quantity
import Text.Token
import Text.Lexer
import Text.Bounded

import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Util
import Text.PrettyPrint.Prettyprinter.Doc

import Idrall.Parser.Lexer
import Idrall.Parser.Rule

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
%name FC fc

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
  | EApp FC (Expr a) (Expr a)
  | EPi FC String (Expr a) (Expr a)
  | EBoolLit FC Bool
  | EBoolAnd FC (Expr a) (Expr a)
  | ELet FC String (Expr a) (Expr a)
  | EList FC (List (Expr a))
  | EWith FC (Expr a) (List1 String) (Expr a)

Show (Expr a) where
  show (EVar fc x) = "(\{show fc}:EVar \{show x})"
  show (EApp fc x y) = "(\{show fc}:EApp \{show x} \{show y})"
  show (EPi fc n x y) = "(\{show fc}:EPi \{show n} \{show x} \{show y})"
  show (EBoolLit fc x) = "\{show fc}:EBoolLit \{show x}"
  show (EBoolAnd fc x y) = "(\{show fc}:EBoolAnd \{show x} \{show y})"
  show (ELet fc x y z) = "(\{show fc}:ELet \{show fc} \{show x} \{show y} \{show z})"
  show (EList fc x) = "(\{show fc}:EList \{show fc} \{show x})"
  show (EWith fc x s y) = "(\{show fc}:EWith \{show fc} \{show x} \{show s} \{show y})"


prettyDottedList : List String -> Doc ann
prettyDottedList [] = pretty ""
prettyDottedList (x :: []) = pretty x
prettyDottedList (x :: xs) = pretty x <+> pretty "." <+> prettyDottedList xs

Pretty (Expr ()) where
  pretty (EVar fc x) = pretty x
  pretty (EBoolLit fc x) = pretty $ show x
  pretty (EApp fc x y) = pretty x <++> pretty y
  pretty (EPi fc "_" x y) = pretty x <++> pretty "->" <++> pretty y
  pretty (EPi fc n x y) =
    pretty "forall(" <+> pretty n <++> pretty ":" <++> pretty x <+> pretty ")"
      <++> pretty "->" <++> pretty y
  pretty (EBoolAnd fc x y) = pretty x <++> pretty "&&" <++> pretty y
  pretty (ELet fc x y z) = pretty "let" <+> pretty x <+> pretty y <+> pretty z
  pretty (EList fc xs) = pretty xs
  pretty (EWith fc x xs y) =
    pretty x <++> pretty "with" <++>
    prettyDottedList (forget xs) <++> pretty "=" <++> pretty y

getBounds : Expr a -> FC
getBounds (EVar x _) = x
getBounds (EApp x _ _) = x
getBounds (EPi x _ _ _) = x
getBounds (EBoolLit x _) = x
getBounds (EBoolAnd x _ _) = x
getBounds (ELet x _ _ _) = x
getBounds (EList x _) = x
getBounds (EWith x _ _ _) = x

updateBounds : FC -> Expr a -> Expr a
updateBounds x (EVar _ z) = EVar x z
updateBounds x (EApp _ z w) = EApp x z w
updateBounds x (EPi _ n z w) = EPi x n z w
updateBounds x (EBoolLit _ z) = EBoolLit x z
updateBounds x (EBoolAnd _ z w) = EBoolAnd x z w
updateBounds x (ELet _ z w v) = ELet x z w v
updateBounds x (EList _ z) = EList x z
updateBounds x (EWith _ z s y) = EWith x z s y

public export
Rule : Type -> Type -> Type
Rule state ty = Grammar state RawToken True ty

public export
EmptyRule : Type -> Type -> Type
EmptyRule state ty = Grammar state RawToken False ty

chainr1 : Grammar state t True (a)
       -> Grammar state t True (a -> a -> a)
       -> Grammar state t True (a)
chainr1 p op = p >>= rest
where
  rest : a -> Grammar state t False (a)
  rest a1 = (do f <- op
                a2 <- p >>= rest
                rest (f a1 a2)) <|> pure a1

chainl1 : Grammar state t True (a)
       -> Grammar state t True (a -> a -> a)
       -> Grammar state t True (a)
chainl1 p op = do
  x <- p
  rest x
where
  rest : a -> Grammar state t False (a)
  rest a1 = (do
    f <- op
    a2 <- p
    rest (f a1 a2)) <|> pure a1

infixOp : Grammar state t True ()
        -> (a -> a -> a)
        -> Grammar state t True (a -> a -> a)
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
  _ <- optional whitespace
  pure x

mutual
  builtinTerm : WithBounds String -> Grammar state (TokenRawToken) False (Expr ())
  builtinTerm _ = fail "TODO not implemented"

  boolLit : WithBounds String -> Grammar state (TokenRawToken) False (Expr ())
  boolLit b@(MkBounded "True" isIrrelevant bounds) = pure $ EBoolLit (boundToFC Nothing b) True
  boolLit b@(MkBounded "False" isIrrelevant bounds) = pure $ EBoolLit (boundToFC Nothing b) False
  boolLit (MkBounded _ isIrrelevant bounds) = fail "unrecognised const"

  varTerm : Grammar state (TokenRawToken) True (Expr ())
  varTerm = do
      name <- bounds $ identPart
      builtinTerm name <|> boolLit name <|> toVar (isKeyword name)
  where
    isKeyword : WithBounds String -> Maybe $ Expr ()
    isKeyword b@(MkBounded val isIrrelevant bounds) =
      let isKeyword = elem val keywords
      in case (isKeyword) of
              (True) => Nothing
              (False) => pure $ EVar (boundToFC Nothing b) val
    toVar : Maybe (Expr ()) -> Grammar state (TokenRawToken) False (Expr ())
    toVar Nothing = fail "is reserved word"
    toVar (Just x) = pure x

  letBinding : Grammar state (TokenRawToken) True (Expr ())
  letBinding = do
    start <- bounds $ tokenW $ keyword "let"
    name <- tokenW $ identPart
    xxx <- tokenW $ symbol "="
    e <- exprTerm
    xxx <- whitespace
    end <- bounds $ tokenW $ keyword "in" -- TODO is this a good end position?
    e' <- exprTerm
    pure $ ELet (mergeBounds (boundToFC Nothing start) (boundToFC Nothing end)) name e e'

  atom : Grammar state (TokenRawToken) True (Expr ())
  atom = do
    a <- varTerm <|> listExpr <|> (between (symbol "(") (symbol ")") exprTerm)
    pure a

  listExpr : Grammar state (TokenRawToken) True (Expr ())
  listExpr = emptyList <|> populatedList
  where
    emptyList : Grammar state (TokenRawToken) True (Expr ())
    emptyList = do
      start <- bounds $ symbol "["
      end <- bounds $ symbol "]"
      pure $ EList (mergeBounds (boundToFC Nothing start) (boundToFC Nothing end)) []
    populatedList : Grammar state (TokenRawToken) True (Expr ())
    populatedList = do
      start <- bounds $ symbol "["
      es <- sepBy1 (symbol ",") exprTerm
      end <- bounds $ symbol "]"
      pure $ EList (mergeBounds (boundToFC Nothing start) (boundToFC Nothing end)) (forget es)

  boolOp : FC -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
  boolOp fc =
    infixOp (do
      _ <- optional whitespace
      tokenW $ symbol "&&")
      (boundedOp EBoolAnd)

  piOp : FC -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
  piOp fc =
    infixOp (do
      _ <- optional whitespace
      tokenW $ symbol "->")
      (boundedOp $ epi' "foo")
  where
    epi' : String -> FC -> Expr a -> Expr a -> Expr a
    epi' n fc y z = EPi fc n y z

  appOp : FC -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
  appOp fc = infixOp whitespace (boundedOp EApp)

  withOp : FC -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
  withOp fc =
    do
      -- TODO find a better solution than just `match White` at the start of
      -- every operator
      _ <- optional $ whitespace
      tokenW $ keyword "with"
      dl <- dottedList
      _ <- optional $ whitespace
      tokenW $ symbol "="
      pure (boundedOp (with' dl))
  where
    with' : List1 String -> FC -> Expr a -> Expr a -> Expr a
    with' xs fc x y = EWith fc x xs y

  boolTerm : Grammar state (TokenRawToken) True (Expr ())
  boolTerm = chainl1 atom (boolOp EmptyFC)

  piTerm : Grammar state (TokenRawToken) True (Expr ())
  piTerm = chainr1 boolTerm (piOp EmptyFC)

  appTerm : Grammar state (TokenRawToken) True (Expr ())
  appTerm = chainl1 piTerm (appOp EmptyFC)

  exprTerm : Grammar state (TokenRawToken) True (Expr ())
  exprTerm = do
    letBinding <|>
    chainl1 appTerm (withOp EmptyFC)

finalParser : Grammar state (TokenRawToken) True (Expr ())
finalParser = do
  e <- exprTerm
  eof
  pure e

Show (ParsingError (TokenRawToken)) where
  show (Error x xs) =
    """
    error: \{x}
    tokens: \{show xs}
    """

removeComments : List (WithBounds TokenRawToken) -> List (WithBounds TokenRawToken)
removeComments xs = filter pred xs
where
  pred : WithBounds RawToken -> Bool
  pred bounds = let tok = val bounds in
    case tok of
         Comment _ => False
         _ => True

doParse' : String -> Either e a

doParse : String -> IO ()
doParse input = do
  Right tokens <- pure $ Idrall.Parser.Lexer.lex input
    | Left e => printLn $ show e
  putStrLn $ "tokens: " ++ show tokens

  Right (expr, x) <- pure $ parse exprTerm tokens -- TODO use finalParser
    | Left e => printLn $ show e

  let doc = the (Doc (Expr ())) $ pretty expr
  putStrLn $
    """
    expr: \{show expr}
    x: \{show x}
    pretty: \{show doc}
    """

normalString : String
normalString = "\"foo\""

interpString : String
interpString = "\"fo ${True && \"ba ${False} r\"} o\""
