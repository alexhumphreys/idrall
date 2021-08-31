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

boundToFC2 : OriginDesc -> WithBounds t -> WithBounds t -> FC
boundToFC2 mbModIdent s e = MkFC mbModIdent (both cast $ start s) (both cast $ end e)

initBounds : OriginDesc
initBounds = Nothing

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

mutual
  public export
  data Chunks a = MkChunks (List (String, Expr a)) String

  ||| Raw AST representation generated directly from the parser
  data Expr a
    -- = EConst U
    = EVar FC String -- | EVar Name Int
    -- | ELam Name (Expr a) (Expr a)
    | EPi FC String (Expr a) (Expr a) -- | EPi Name (Expr a) (Expr a)
    | EApp FC (Expr a) (Expr a) -- | EApp (Expr a) (Expr a)
    | ELet FC String (Expr a) (Expr a) -- | ELet Name (Maybe (Expr a)) (Expr a) (Expr a)
    -- | EAnnot (Expr a) (Expr a)
    -- | EBool
    | EBoolLit FC Bool -- | EBoolLit Bool
    | EBoolAnd FC (Expr a) (Expr a) -- | EBoolAnd (Expr a) (Expr a)
    -- | EBoolOr  (Expr a) (Expr a)
    -- | EBoolEQ  (Expr a) (Expr a)
    -- | EBoolNE  (Expr a) (Expr a)
    -- | EBoolIf (Expr a) (Expr a) (Expr a)
    -- | ENatural
    -- | ENaturalLit Nat
    | ENaturalFold FC -- | ENaturalFold
    | ENaturalBuild FC -- | ENaturalBuild
    | ENaturalIsZero FC -- | ENaturalIsZero
    | ENaturalEven FC -- | ENaturalEven
    | ENaturalOdd FC -- | ENaturalOdd
    | ENaturalToInteger FC -- | ENaturalToInteger
    | ENaturalSubtract FC -- | ENaturalSubtract
    | ENaturalShow FC -- | ENaturalShow
    -- | ENaturalPlus (Expr a) (Expr a)
    -- | ENaturalTimes (Expr a) (Expr a)
    -- | EInteger
    -- | EIntegerLit Integer
    | EIntegerShow FC -- | EIntegerShow
    | EIntegerClamp FC -- | EIntegerClamp
    | EIntegerNegate FC -- | EIntegerNegate
    | EIntegerToDouble FC -- | EIntegerToDouble
    -- | EDouble
    | EDoubleLit FC Double -- | EDoubleLit Double
    | EDoubleShow FC -- | EDoubleShow
    -- | EText
    | ETextLit FC (Chunks a) -- | ETextLit (Chunks a)
    -- | ETextAppend (Expr a) (Expr a)
    | ETextShow FC -- | ETextShow
    | ETextReplace FC -- | ETextReplace
    | EList FC -- | EList
    | EListLit FC (List (Expr a)) -- | EListLit (Maybe (Expr a)) (List (Expr a))
    -- | EListAppend (Expr a) (Expr a)
    | EListBuild FC -- | EListBuild
    | EListFold FC -- | EListFold
    | EListLength FC -- | EListLength
    | EListHead FC -- | EListHead
    | EListLast FC -- | EListLast
    | EListIndexed FC -- | EListIndexed
    | EListReverse FC -- | EListReverse
    | EOptional FC -- | EOptional
    | ENone FC -- | ENone
    -- | ESome (Expr a)
    -- | EEquivalent (Expr a) (Expr a)
    -- | EAssert (Expr a)
    -- | ERecord (SortedMap FieldName (Expr a))
    -- | ERecordLit (SortedMap FieldName (Expr a))
    -- | EUnion (SortedMap FieldName (Maybe (Expr a)))
    -- | ECombine (Expr a) (Expr a)
    -- | ECombineTypes (Expr a) (Expr a)
    -- | EPrefer (Expr a) (Expr a)
    -- | ERecordCompletion (Expr a) (Expr a)
    -- | EMerge (Expr a) (Expr a) (Maybe (Expr a))
    -- | EToMap (Expr a) (Maybe (Expr a))
    -- | EField (Expr a) FieldName
    -- | EProject (Expr a) (Either (List FieldName) (Expr a))
    | EWith FC (Expr a) (List1 String) (Expr a) -- | EWith (Expr a) (List1 FieldName) (Expr a)
    -- | EImportAlt (Expr a) (Expr a)
    | EEmbed FC String -- | EEmbed (Import a)

mkExprFC : OriginDesc -> WithBounds x -> (FC -> x -> Expr a) -> Expr a
mkExprFC od e mkE = mkE (boundToFC od e) (val e)

mkExprFC0 : OriginDesc -> WithBounds x -> (FC -> Expr a) -> Expr a
mkExprFC0 od e mkE = mkE (boundToFC od e)

getBounds : Expr a -> FC
getBounds (EVar fc _) = fc
getBounds (EApp fc _ _) = fc
getBounds (EPi fc _ _ _) = fc
getBounds (EDoubleLit fc _) = fc
getBounds (EBoolLit fc _) = fc
getBounds (EBoolAnd fc _ _) = fc
getBounds (ELet fc _ _ _) = fc
getBounds (EListLit fc _) = fc
getBounds (EWith fc _ _ _) = fc
getBounds (ETextLit fc _) = fc
getBounds (ENaturalBuild fc) = fc
getBounds (ENaturalFold fc) = fc
getBounds (ENaturalIsZero fc) = fc
getBounds (ENaturalEven fc) = fc
getBounds (ENaturalOdd fc) = fc
getBounds (ENaturalSubtract fc) = fc
getBounds (ENaturalToInteger fc) = fc
getBounds (ENaturalShow fc) = fc
getBounds (EIntegerShow fc) = fc
getBounds (EIntegerNegate fc) = fc
getBounds (EIntegerClamp fc) = fc
getBounds (EIntegerToDouble fc) = fc
getBounds (EDoubleShow fc) = fc
getBounds (EListBuild fc) = fc
getBounds (EListFold fc) = fc
getBounds (EListLength fc) = fc
getBounds (EListHead fc) = fc
getBounds (EListLast fc) = fc
getBounds (EListIndexed fc) = fc
getBounds (EListReverse fc) = fc
getBounds (EList fc) = fc
getBounds (ETextShow fc) = fc
getBounds (ETextReplace fc) = fc
getBounds (ENone fc) = fc
getBounds (EOptional fc) = fc
getBounds (EEmbed fc _) = fc

updateBounds : FC -> Expr a -> Expr a
updateBounds fc (EVar _ z) = EVar fc z
updateBounds fc (EApp _ z w) = EApp fc z w
updateBounds fc (EPi _ n z w) = EPi fc n z w
updateBounds fc (EDoubleLit _ z) = EDoubleLit fc z
updateBounds fc (EBoolLit _ z) = EBoolLit fc z
updateBounds fc (EBoolAnd _ z w) = EBoolAnd fc z w
updateBounds fc (ELet _ z w v) = ELet fc z w v
updateBounds fc (EListLit _ z) = EListLit fc z
updateBounds fc (EWith _ z s y) = EWith fc z s y
updateBounds fc (ETextLit _ z) = ETextLit fc z
updateBounds fc (ENaturalBuild _) = ENaturalBuild fc
updateBounds fc (ENaturalFold _) = ENaturalFold fc
updateBounds fc (ENaturalIsZero _) = ENaturalIsZero fc
updateBounds fc (ENaturalEven _) = ENaturalEven fc
updateBounds fc (ENaturalOdd _) = ENaturalOdd fc
updateBounds fc (ENaturalSubtract _) = ENaturalSubtract fc
updateBounds fc (ENaturalToInteger _) = ENaturalToInteger fc
updateBounds fc (ENaturalShow _) = ENaturalShow fc
updateBounds fc (EIntegerShow _) = EIntegerShow fc
updateBounds fc (EIntegerNegate _) = EIntegerNegate fc
updateBounds fc (EIntegerClamp _) = EIntegerClamp fc
updateBounds fc (EIntegerToDouble _) = EIntegerToDouble fc
updateBounds fc (EDoubleShow _) = EDoubleShow fc
updateBounds fc (EListBuild _) = EListBuild fc
updateBounds fc (EListFold _) = EListFold fc
updateBounds fc (EListLength _) = EListLength fc
updateBounds fc (EListHead _) = EListHead fc
updateBounds fc (EListLast _) = EListLast fc
updateBounds fc (EListIndexed _) = EListIndexed fc
updateBounds fc (EListReverse _) = EListReverse fc
updateBounds fc (EList _) = EList fc
updateBounds fc (ETextShow _) = ETextShow fc
updateBounds fc (ETextReplace _) = ETextReplace fc
updateBounds fc (ENone _) = ENone fc
updateBounds fc (EOptional _) = EOptional fc
updateBounds fc (EEmbed _ z) = EEmbed fc z

public export
Semigroup (Chunks a) where
  (<+>) (MkChunks xysL zL) (MkChunks [] zR) = MkChunks xysL (zL <+> zR)
  (<+>) (MkChunks xysL zL) (MkChunks ((x, y) :: xysR) zR) =
    MkChunks (xysL ++ (zL <+> x, y)::xysR) zR

public export
Monoid (Chunks a) where
  neutral = MkChunks [] neutral

mutual
  Show (Chunks a) where
    show (MkChunks xs x) = "MkChunks \{show xs} \{show x}"

  Show (Expr a) where
    show (EVar fc x) = "(\{show fc}:EVar \{show x})"
    show (EApp fc x y) = "(\{show fc}:EApp \{show x} \{show y})"
    show (EPi fc n x y) = "(\{show fc}:EPi \{show n} \{show x} \{show y})"
    show (EDoubleLit fc x) = "\{show fc}:EDoubleLit \{show x}"
    show (EBoolLit fc x) = "\{show fc}:EBoolLit \{show x}"
    show (EBoolAnd fc x y) = "(\{show fc}:EBoolAnd \{show x} \{show y})"
    show (ELet fc x y z) = "(\{show fc}:ELet \{show fc} \{show x} \{show y} \{show z})"
    show (EListLit fc x) = "(\{show fc}:EListLit \{show fc} \{show x})"
    show (EWith fc x s y) = "(\{show fc}:EWith \{show fc} \{show x} \{show s} \{show y})"
    show (ETextLit fc cs) = "(\{show fc}:ETextLit \{show fc} \{show cs}"
    show (ENaturalBuild fc) = "(\{show fc}:ENaturalShow)"
    show (ENaturalFold fc) = "(\{show fc}:ENaturalShow)"
    show (ENaturalIsZero fc) = "(\{show fc}:ENaturalShow)"
    show (ENaturalEven fc) = "(\{show fc}:ENaturalShow)"
    show (ENaturalOdd fc) = "(\{show fc}:ENaturalShow)"
    show (ENaturalSubtract fc) = "(\{show fc}:ENaturalShow)"
    show (ENaturalToInteger fc) = "(\{show fc}:ENaturalShow)"
    show (ENaturalShow fc) = "(\{show fc}:ENaturalShow)"
    show (EIntegerShow fc) = "(\{show fc}:EIntegerShow)"
    show (EIntegerNegate fc) = "(\{show fc}:EIntegerShow)"
    show (EIntegerClamp fc) = "(\{show fc}:EIntegerShow)"
    show (EIntegerToDouble fc) = "(\{show fc}:EIntegerShow)"
    show (EDoubleShow fc) = "(\{show fc}:EDoubleShow)"
    show (EListBuild fc) = "(\{show fc}:EListBuild)"
    show (EListFold fc) = "(\{show fc}:EListFold)"
    show (EListLength fc) = "(\{show fc}:EListLength)"
    show (EListHead fc) = "(\{show fc}:EListHead)"
    show (EListLast fc) = "(\{show fc}:EListLast)"
    show (EListIndexed fc) = "(\{show fc}:EListIndexed)"
    show (EListReverse fc) = "(\{show fc}:EListReverse)"
    show (EList fc) = "(\{show fc}:EList)"
    show (ETextShow fc) = "(\{show fc}:ETextShow)"
    show (ETextReplace fc) = "(\{show fc}:ETextReplace)"
    show (ENone fc) = "(\{show fc}:ENone)"
    show (EOptional fc) = "(\{show fc}:EOptional)"
    show (EEmbed fc x) = "(\{show fc}:EEmbed \{show fc} \{show x})"

prettyDottedList : List String -> Doc ann
prettyDottedList [] = pretty ""
prettyDottedList (x :: []) = pretty x
prettyDottedList (x :: xs) = pretty x <+> pretty "." <+> prettyDottedList xs

mutual
  Pretty (Chunks ()) where
    pretty (MkChunks xs x) = pretty xs <+> pretty x

  Pretty (Expr ()) where
    pretty (EVar fc x) = pretty x
    pretty (EApp fc x y) = pretty x <++> pretty y
    pretty (EPi fc "_" x y) = pretty x <++> pretty "->" <++> pretty y
    pretty (EPi fc n x y) =
      pretty "forall(" <+> pretty n <++> pretty ":" <++> pretty x <+> pretty ")"
        <++> pretty "->" <++> pretty y
    pretty (EDoubleLit fc x) = pretty $ show x
    pretty (EBoolLit fc x) = pretty $ show x
    pretty (EBoolAnd fc x y) = pretty x <++> pretty "&&" <++> pretty y
    pretty (ELet fc x y z) = pretty "let" <+> pretty x <+> pretty y <+> pretty z
    pretty (EListLit fc xs) = pretty xs
    pretty (EWith fc x xs y) =
      pretty x <++> pretty "with" <++>
      prettyDottedList (forget xs) <++> pretty "=" <++> pretty y
    pretty (ETextLit fc cs) = pretty cs
    pretty (ENaturalBuild fc) = pretty "Natural/build"
    pretty (ENaturalFold fc) = pretty "Natural/fold"
    pretty (ENaturalIsZero fc) = pretty "Natural/isZero"
    pretty (ENaturalEven fc) = pretty "Natural/Even"
    pretty (ENaturalOdd fc) = pretty "Natural/Odd"
    pretty (ENaturalSubtract fc) = pretty "Natural/subtract"
    pretty (ENaturalToInteger fc) = pretty "Natural/toInteger"
    pretty (ENaturalShow fc) = pretty "Natural/show"
    pretty (EIntegerShow fc) = pretty "Integer/show"
    pretty (EIntegerNegate fc) = pretty "Integer/negate"
    pretty (EIntegerClamp fc) = pretty "Integer/clamp"
    pretty (EIntegerToDouble fc) = pretty "Integer/toDouble"
    pretty (EDoubleShow fc) = pretty "Double/show"
    pretty (EListBuild fc) = pretty "List/build"
    pretty (EListFold fc) = pretty "List/fold"
    pretty (EListLength fc) = pretty "List/length"
    pretty (EListHead fc) = pretty "List/head"
    pretty (EListLast fc) = pretty "List/last"
    pretty (EListIndexed fc) = pretty "List/indexed"
    pretty (EListReverse fc) = pretty "List/indexed"
    pretty (EList fc) = pretty "List"
    pretty (ETextShow fc) = pretty "Text/show"
    pretty (ETextReplace fc) = pretty "Text/replace"
    pretty (ENone fc) = pretty "None"
    pretty (EOptional fc) = pretty "Optional"
    pretty (EEmbed fc x) = pretty x

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

builtinTerm : WithBounds String -> Grammar state (TokenRawToken) False (Expr ())
builtinTerm str =
  case val str of
     "Natural/build" => pure $ cons ENaturalBuild
     "Natural/fold" => pure $ cons ENaturalFold
     "Natural/isZero" => pure $ cons ENaturalIsZero
     "Natural/even" => pure $ cons ENaturalEven
     "Natural/odd" => pure $ cons ENaturalOdd
     "Natural/subtract" => pure $ cons ENaturalSubtract
     "Natural/toInteger" => pure $ cons ENaturalToInteger
     "Natural/show" => pure $ cons ENaturalShow
     "Integer/show" => pure $ cons EIntegerShow
     "Integer/negate" => pure $ cons EIntegerNegate
     "Integer/clamp" => pure $ cons EIntegerClamp
     "Integer/toDouble" => pure $ cons EIntegerToDouble
     "Double/show" => pure $ cons EDoubleShow
     "List/build" => pure $ cons EListBuild
     "List/fold" => pure $ cons EListFold
     "List/length" => pure $ cons EListLength
     "List/head" => pure $ cons EListHead
     "List/last" => pure $ cons EListLast
     "List/indexed" => pure $ cons EListIndexed
     "List/reverse" => pure $ cons EListReverse
     "List" => pure $ cons EList
     "Text/show" => pure $ cons ETextShow
     "Text/replace" => pure $ cons ETextReplace
     "None" => pure $ cons ENone
     "Optional" => pure $ cons EOptional
     "NaN" => pure $ EDoubleLit (boundToFC initBounds str) (0.0/0.0)
     x => fail "Expected builtin name"
  where
    cons : (FC -> Expr ()) -> Expr ()
    cons = mkExprFC0 initBounds str

mutual
  embed : Grammar state (TokenRawToken) True (Expr ())
  embed = do
    s <- bounds $ embedPath
    pure $ mkExprFC initBounds s EEmbed

  doubleLit : Grammar state (TokenRawToken) True (Expr ())
  doubleLit = do
    s <- bounds $ Rule.doubleLit
    pure $ mkExprFC initBounds s EDoubleLit

  textLit : Grammar state (TokenRawToken) True (Expr ())
  textLit = do
    start <- bounds $ textBoundary
    chunks <- some (interpLit <|> chunkLit)
    end <- bounds $ textBoundary
    pure $ ETextLit (boundToFC2 initBounds start end) (foldl (<+>) neutral chunks)
  where
    interpLit : Rule (Chunks ())
    interpLit = do
      e <- between interpBegin interpEnd exprTerm
      pure $ MkChunks [("", e)] ""

    chunkLit : Rule (Chunks ())
    chunkLit = do
      str <- Parser.Rule.textLit
      pure (MkChunks [] str)

  boolLit : WithBounds String -> Grammar state (TokenRawToken) False (Expr ())
  boolLit b@(MkBounded "True" isIrrelevant bounds) = pure $ EBoolLit (boundToFC initBounds b) True
  boolLit b@(MkBounded "False" isIrrelevant bounds) = pure $ EBoolLit (boundToFC initBounds b) False
  boolLit (MkBounded _ isIrrelevant bounds) = fail "unrecognised const"

  builtin : Grammar state (TokenRawToken) True (Expr ())
  builtin = do
      name <- bounds $ Rule.builtin
      builtinTerm name

  varTerm : Grammar state (TokenRawToken) True (Expr ())
  varTerm = do
      name <- bounds $ identPart
      boolLit name <|> toVar (isKeyword name)
  where
    isKeyword : WithBounds String -> Maybe $ Expr ()
    isKeyword b@(MkBounded val isIrrelevant bounds) =
      let isKeyword = elem val keywords
      in case (isKeyword) of
              (True) => Nothing
              (False) => pure $ EVar (boundToFC initBounds b) val
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
    pure $ ELet (mergeBounds (boundToFC initBounds start) (boundToFC initBounds end)) name e e'

  atom : Grammar state (TokenRawToken) True (Expr ())
  atom = do
    a <- varTerm <|> textLit
      <|> doubleLit
      <|> builtin <|> embed
      <|> listExpr <|> (between (symbol "(") (symbol ")") exprTerm)
    pure a

  listExpr : Grammar state (TokenRawToken) True (Expr ())
  listExpr = emptyList <|> populatedList
  where
    emptyList : Grammar state (TokenRawToken) True (Expr ())
    emptyList = do
      start <- bounds $ symbol "["
      end <- bounds $ symbol "]"
      pure $ EListLit (mergeBounds (boundToFC initBounds start) (boundToFC initBounds end)) []
    populatedList : Grammar state (TokenRawToken) True (Expr ())
    populatedList = do
      start <- bounds $ symbol "["
      es <- sepBy1 (symbol ",") exprTerm
      end <- bounds $ symbol "]"
      pure $ EListLit (mergeBounds (boundToFC initBounds start) (boundToFC initBounds end)) (forget es)

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
normalString = "\"f\noo\""

interpString : String
interpString = "\"fo ${True && \"ba ${False} r\"} o\""
