module Idrall.ParserNew

import Data.List
import Data.List1
import Data.String -- needed for pretty?
import Data.SortedMap

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
import Idrall.FC
import Idrall.Expr
import Idrall.Path
import Debug.Trace

public export
RawExpr : Type
RawExpr = Expr ImportStatement

both : (a -> b) -> (a, a) -> (b, b)
both f x = (f (fst x), f (snd x))

boundToFC : OriginDesc -> WithBounds t -> FC
boundToFC mbModIdent b = MkFC mbModIdent (both cast $ start b) (both cast $ end b)

boundToFC2 : OriginDesc -> WithBounds t -> WithBounds u -> FC
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

mkExprFC : OriginDesc -> WithBounds x -> (FC -> x -> Expr a) -> Expr a
mkExprFC od e mkE = mkE (boundToFC od e) (val e)

mkExprFC0 : OriginDesc -> WithBounds x -> (FC -> Expr a) -> Expr a
mkExprFC0 od e mkE = mkE (boundToFC od e)

updateBounds : FC -> Expr a -> Expr a
updateBounds fc (EConst _ z) = EConst fc z
updateBounds fc (EVar _ z n) = EVar fc z n
updateBounds fc (ELam _ z w v) = ELam fc z w v
updateBounds fc (EApp _ z w) = EApp fc z w
updateBounds fc (EPi _ n z w) = EPi fc n z w
updateBounds fc (ELet _ z t w v) = ELet fc z t w v
updateBounds fc (EAnnot _ z w) = EAnnot fc z w
updateBounds fc (EBool _) = EBool fc
updateBounds fc (EBoolLit _ z) = EBoolLit fc z
updateBounds fc (EBoolAnd _ z w) = EBoolAnd fc z w
updateBounds fc (EBoolOr _ z w) = EBoolOr fc z w
updateBounds fc (EBoolEQ _ z w) = EBoolEQ fc z w
updateBounds fc (EBoolNE _ z w) = EBoolNE fc z w
updateBounds fc (EBoolIf _ z w v) = EBoolIf fc z w v
updateBounds fc (ENatural _) = ENatural fc
updateBounds fc (ENaturalLit _ x) = ENaturalLit fc x
updateBounds fc (ENaturalBuild _) = ENaturalBuild fc
updateBounds fc (ENaturalFold _) = ENaturalFold fc
updateBounds fc (ENaturalIsZero _) = ENaturalIsZero fc
updateBounds fc (ENaturalEven _) = ENaturalEven fc
updateBounds fc (ENaturalOdd _) = ENaturalOdd fc
updateBounds fc (ENaturalSubtract _) = ENaturalSubtract fc
updateBounds fc (ENaturalToInteger _) = ENaturalToInteger fc
updateBounds fc (ENaturalShow _) = ENaturalShow fc
updateBounds fc (ENaturalPlus _ z w) = ENaturalPlus fc z w
updateBounds fc (ENaturalTimes _ z w) = ENaturalTimes fc z w
updateBounds fc (EInteger _) = EInteger fc
updateBounds fc (EIntegerLit _ x) = EIntegerLit fc x
updateBounds fc (EIntegerShow _) = EIntegerShow fc
updateBounds fc (EIntegerNegate _) = EIntegerNegate fc
updateBounds fc (EIntegerClamp _) = EIntegerClamp fc
updateBounds fc (EIntegerToDouble _) = EIntegerToDouble fc
updateBounds fc (EDouble _) = EDouble fc
updateBounds fc (EDoubleShow _) = EDoubleShow fc
updateBounds fc (EDoubleLit _ z) = EDoubleLit fc z
updateBounds fc (EList _) = EList fc
updateBounds fc (EListLit _ t z) = EListLit fc t z
updateBounds fc (EListAppend _ z w) = EListAppend fc z w
updateBounds fc (EListBuild _) = EListBuild fc
updateBounds fc (EListFold _) = EListFold fc
updateBounds fc (EListLength _) = EListLength fc
updateBounds fc (EListHead _) = EListHead fc
updateBounds fc (EListLast _) = EListLast fc
updateBounds fc (EListIndexed _) = EListIndexed fc
updateBounds fc (EListReverse _) = EListReverse fc
updateBounds fc (EText _) = EText fc
updateBounds fc (ETextLit _ z) = ETextLit fc z
updateBounds fc (ETextAppend _ z w) = ETextAppend fc z w
updateBounds fc (ETextShow _) = ETextShow fc
updateBounds fc (ETextReplace _) = ETextReplace fc
updateBounds fc (EOptional _) = EOptional fc
updateBounds fc (ESome _ x) = ESome fc x
updateBounds fc (ENone _) = ENone fc
updateBounds fc (EField _ z s) = EField fc z s
updateBounds fc (EWith _ z s y) = EWith fc z s y
updateBounds fc (EEquivalent _ z w) = EEquivalent fc z w
updateBounds fc (EAssert _ z) = EAssert fc z
updateBounds fc (ERecord _ z) = ERecord fc z
updateBounds fc (ERecordLit _ z) = ERecordLit fc z
updateBounds fc (EUnion _ z) = EUnion fc z
updateBounds fc (ECombine _ x y) = ECombine fc x y
updateBounds fc (ECombineTypes _ x y) = ECombineTypes fc x y
updateBounds fc (EPrefer _ x y) = EPrefer fc x y
updateBounds fc (ERecordCompletion _ x y) = ERecordCompletion fc x y
updateBounds fc (EMerge _ x y z) = EMerge fc x y z
updateBounds fc (EToMap _ x y) = EToMap fc x y
updateBounds fc (EProject _ x y) = EProject fc x y
updateBounds fc (EImportAlt _ x y) = EImportAlt fc x y
updateBounds fc (EEmbed _ z) = EEmbed fc z

prettyDottedList : Pretty a => List a -> Doc ann
prettyDottedList [] = pretty ""
prettyDottedList (x :: []) = pretty x
prettyDottedList (x :: xs) = pretty x <+> pretty "." <+> prettyDottedList xs

mutual
  prettySortedMap : Pretty x => Pretty y
                  => (Doc ann -> Doc ann)
                  -> Doc ann
                  -> (SortedMap x y)
                  -> Doc ann
  prettySortedMap wrapping sign e =
    let ls = SortedMap.toList e
        lsDoc = map (go sign) ls
    in
    wrapping $ foldl (<++>) neutral (punctuate comma lsDoc)
  where
    go : Doc ann -> (x, y) -> Doc ann
    go x (s, e) = pretty s <++> x <++> pretty e

  prettyUnion : Pretty x => Pretty y
              => (SortedMap x (Maybe y))
              -> Doc ann
  prettyUnion e =
    let ls = SortedMap.toList e
        lsDoc = map go ls
    in
    enclose langle (space <+> rangle) $ foldl (<++>) neutral (punctuate (space <+> pipe) lsDoc)
  where
    go : (x, Maybe y) -> Doc ann
    go (s, Nothing) = pretty s
    go (s, Just e) = pretty s <++> colon <++> pretty e

  Pretty U where
    pretty CType = "Type"
    pretty Sort = "Sort"
    pretty Kind = "Kind"

  Pretty FieldName where
    pretty (MkFieldName x) = pretty x

  Pretty FilePath where
    pretty (MkFilePath path Nothing) = pretty $ prettyPrintPath path
    pretty (MkFilePath path (Just x)) =
      (pretty $ prettyPrintPath path) <+> pretty "/" <+> pretty x

  Pretty ImportStatement where
    pretty (LocalFile x) = pretty x
    pretty (EnvVar x) = pretty "env:" <+> pretty x
    pretty (Http x) = pretty x
    pretty Missing = pretty "Missing"

  Pretty a => Pretty (Import a) where
    pretty (Raw x) = pretty x
    pretty (Text x) = pretty x <++> pretty "as Text"
    pretty (Location x) = pretty x <++> pretty "as Location"
    pretty (Resolved x) = pretty "ERROR: SHOULD NOT BE"

  Pretty a => Pretty (Chunks a) where
    pretty (MkChunks xs x) = pretty xs <+> pretty x

  Pretty a => Pretty (Expr a) where
    pretty (EConst fc x) = pretty x
    pretty (EVar fc x n) = pretty x <+> pretty "@" <+> pretty n
    pretty (EApp fc x y) = pretty x <++> pretty y
    pretty (ELam fc n x y) =
      pretty "\\" <+> parens (pretty n <++> colon <++> pretty x)
        <++> pretty "->" <++> pretty y
    pretty (EPi fc "_" x y) = pretty x <++> pretty "->" <++> pretty y
    pretty (EPi fc n x y) =
      pretty "forall" <+> parens (pretty n <++> colon <++> pretty x)
        <++> pretty "->" <++> pretty y
    pretty (ELet fc x t y z) =
      pretty "let" <++> pretty x <++> equals <++> pretty y
        <++> pretty "in" <++> pretty z
    pretty (EAnnot fc x y) = pretty x <++> colon <++> pretty y
    pretty (EBool fc) = pretty "Bool"
    pretty (EBoolLit fc x) = pretty $ show x
    pretty (EBoolAnd fc x y) = pretty x <++> pretty "&&" <++> pretty y
    pretty (EBoolOr fc x y) = pretty x <++> pretty "||" <++> pretty y
    pretty (EBoolEQ fc x y) = pretty x <++> pretty "==" <++> pretty y
    pretty (EBoolNE fc x y) = pretty x <++> pretty "!=" <++> pretty y
    pretty (EBoolIf fc x y z) =
      pretty "if" <++> pretty x
      <++> pretty "then" <++> pretty y
      <++> pretty "else" <++> pretty z
    pretty (ENatural fc) = pretty "Natural"
    pretty (ENaturalLit fc x) = pretty x
    pretty (ENaturalBuild fc) = pretty "Natural/build"
    pretty (ENaturalFold fc) = pretty "Natural/fold"
    pretty (ENaturalIsZero fc) = pretty "Natural/isZero"
    pretty (ENaturalEven fc) = pretty "Natural/Even"
    pretty (ENaturalOdd fc) = pretty "Natural/Odd"
    pretty (ENaturalSubtract fc) = pretty "Natural/subtract"
    pretty (ENaturalToInteger fc) = pretty "Natural/toInteger"
    pretty (ENaturalShow fc) = pretty "Natural/show"
    pretty (ENaturalPlus fc x y) = pretty x <++> pretty "+" <++> pretty y
    pretty (ENaturalTimes fc x y) = pretty x <++> pretty "*" <++> pretty y
    pretty (EInteger fc) = pretty "Integer"
    pretty (EIntegerLit fc x) = pretty x
    pretty (EIntegerShow fc) = pretty "Integer/show"
    pretty (EIntegerNegate fc) = pretty "Integer/negate"
    pretty (EIntegerClamp fc) = pretty "Integer/clamp"
    pretty (EIntegerToDouble fc) = pretty "Integer/toDouble"
    pretty (EDouble fc) = pretty "Double"
    pretty (EDoubleLit fc x) = pretty $ show x
    pretty (EDoubleShow fc) = pretty "Double/show"
    pretty (EList fc) = pretty "List"
    pretty (EListLit fc t xs) = pretty xs <++> colon <++> pretty t
    pretty (EListAppend fc x y) = pretty x <++> pretty "#" <++> pretty y
    pretty (EListBuild fc) = pretty "List/build"
    pretty (EListFold fc) = pretty "List/fold"
    pretty (EListLength fc) = pretty "List/length"
    pretty (EListHead fc) = pretty "List/head"
    pretty (EListLast fc) = pretty "List/last"
    pretty (EListIndexed fc) = pretty "List/indexed"
    pretty (EListReverse fc) = pretty "List/indexed"
    pretty (EText fc) = pretty "Text"
    pretty (ETextLit fc cs) = pretty cs
    pretty (ETextAppend fc x y) = pretty x <++> pretty "++" <++> pretty y
    pretty (ETextShow fc) = pretty "Text/show"
    pretty (ETextReplace fc) = pretty "Text/replace"
    pretty (EOptional fc) = pretty "Optional"
    pretty (ESome fc x) = pretty "Some" <++> pretty x
    pretty (ENone fc) = pretty "None"
    pretty (EField fc x y) =
      pretty x <+> pretty "." <+> pretty y
    pretty (EWith fc x xs y) =
      pretty x <++> pretty "with" <++>
      prettyDottedList (forget xs) <++> equals <++> pretty y
    pretty (EEquivalent fc x y) = pretty x <++> pretty "===" <++> pretty y
    pretty (EAssert fc x) = pretty "assert" <++> colon <++> pretty x
    pretty (ERecord fc x) = prettySortedMap braces colon x
    pretty (ERecordLit fc x) = prettySortedMap braces equals x
    pretty (EUnion fc x) = prettyUnion x
    pretty (ECombine fc x y) = pretty x <++> pretty "/\\" <++> pretty y
    pretty (ECombineTypes fc x y) = pretty x <++> pretty "//\\\\" <++> pretty y
    pretty (EPrefer fc x y) = pretty x <++> pretty "//" <++> pretty y
    pretty (ERecordCompletion fc x y) = pretty x <++> pretty "::" <++> pretty y
    pretty (EMerge fc x y Nothing) = pretty "merge" <++> pretty x <++> pretty y
    pretty (EMerge fc x y (Just z)) = pretty "merge" <++> pretty x <++> pretty y <++> pretty ":" <++> pretty z
    pretty (EToMap fc x Nothing) = pretty "toMap" <++> pretty x
    pretty (EProject fc x (Left y)) = pretty x <+> dot <+> braces (pretty y) -- TODO fix
    pretty (EProject fc x (Right y)) = pretty x <+> dot <+> parens (pretty y)
    pretty (EToMap fc x (Just y)) =
      pretty "merge" <++> pretty x
      <++> pretty ":" <++> pretty y
    pretty (EImportAlt fc x y) = pretty x <++> pretty "?" <++> pretty y
    pretty (EEmbed fc x) = pretty x

Rule : Type -> Type -> Type
Rule state ty = Grammar state RawToken True ty

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

hchainl : Grammar state t True (a)
        -> Grammar state t True (a -> b -> a)
        -> Grammar state t True (b)
        -> Grammar state t True (a)
hchainl pini pop parg = pini >>= go
  where
  covering
  go : a -> Grammar state t False (a)
  go x = (do op <- pop
             arg <- parg
             go $ op x arg) <|> pure x

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
  let xB = getFC x
      yB = getFC y
      mB = mergeBounds xB yB in
      op mB x y

builtinTerm : OriginDesc -> WithBounds String -> Grammar state (TokenRawToken) False (RawExpr)
builtinTerm od str =
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
     "Optional" => pure $ cons EOptional
     "None" => pure $ cons ENone
     "NaN" => pure $ EDoubleLit (boundToFC od str) (0.0/0.0)
     "True" => pure $ EBoolLit (boundToFC od str) True
     "False" => pure $ EBoolLit (boundToFC od str) False
     "Bool" => pure $ EBool (boundToFC od str)
     "Text" => pure $ EText (boundToFC od str)
     "Natural" => pure $ ENatural (boundToFC od str)
     "Integer" => pure $ EInteger (boundToFC od str)
     "Double" => pure $ EDouble (boundToFC od str)
     "Type" => pure $ EConst (boundToFC od str) CType
     "Kind" => pure $ EConst (boundToFC od str) Kind
     "Sort" => pure $ EConst (boundToFC od str) Sort
     x => fail "Expected builtin name"
  where
    cons : (FC -> RawExpr) -> RawExpr
    cons = mkExprFC0 od str

mutual
  dhallImport : Grammar state (TokenRawToken) True (ImportStatement)
  dhallImport = httpImport <|> envImport <|> pathImport <|> missingImport
  where
    httpImport : Grammar state (TokenRawToken) True (ImportStatement)
    httpImport = do
      h <- Rule.httpImport
      pure $ Http h
    envImport : Grammar state (TokenRawToken) True (ImportStatement)
    envImport = do
      e <- Rule.envImport
      pure $ EnvVar e
    pathImport : Grammar state (TokenRawToken) True (ImportStatement)
    pathImport = do
      p <- Rule.filePath
      pure $ LocalFile $ filePathFromPath p
    missingImport : Grammar state (TokenRawToken) True (ImportStatement)
    missingImport = Rule.missingImport *> pure Missing

  embed : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  embed od = do
    i <- bounds (shaAndAsImport <|> asImport <|> shaImport <|> bareImport)
    pure $ EEmbed (boundToFC od i) (val i)
  where
    asType : Grammar state (TokenRawToken) True (a -> Import a)
    asType = do
      (tokenW $ keyword "as Text" *> pure Text)
        <|> (tokenW $ keyword "as Location" *> pure Location)
    asImport : Grammar state (TokenRawToken) True (Import ImportStatement)
    asImport = do
      i <- dhallImport
      con <- asType
      pure $ con i
    shaImport : Grammar state (TokenRawToken) True (Import ImportStatement)
    shaImport = do
      i <- dhallImport
      _ <- tokenW $ Rule.shaImport
      pure $ Raw i
    shaAndAsImport : Grammar state (TokenRawToken) True (Import ImportStatement)
    shaAndAsImport = do
      i <- dhallImport
      _ <- tokenW $ Rule.shaImport
      con <- asType
      pure $ con i
    bareImport : Grammar state (TokenRawToken) True (Import ImportStatement)
    bareImport = do
      i <- dhallImport
      pure $ Raw i

  naturalLit : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  naturalLit od = do
    s <- bounds $ Rule.naturalLit
    pure $ mkExprFC od s ENaturalLit

  integerLit : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  integerLit od = do
    s <- bounds $ Rule.integerLit
    pure $ mkExprFC od s EIntegerLit

  doubleLit : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  doubleLit od = do
    s <- bounds $ Rule.doubleLit
    pure $ mkExprFC od s EDoubleLit

  someLit : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  someLit od = do
    start <- bounds $ tokenW $ someBuiltin
    e <- bounds $ exprTerm od
    pure $ ESome (mergeBounds (boundToFC od start) (boundToFC od e)) $ val e

  emptyTextLit : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  emptyTextLit od = do
    start <- bounds $ textBoundary
    end <- bounds $ textBoundary
    pure $ ETextLit (boundToFC2 od start end) neutral

  textLit : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  textLit od = do
    start <- bounds $ textBegin
    chunks <- some (interpLit <|> chunkLit (val start))
    end <- bounds $ textBoundary
    pure $ ETextLit (boundToFC2 od start end) (foldl (<+>) neutral chunks)
  where
    interpLit : Rule (Chunks ImportStatement)
    interpLit = do
      e <- between interpBegin interpEnd $ exprTerm od
      pure $ MkChunks [("", e)] ""

    chunkLit : IsMultiline -> Rule (Chunks ImportStatement)
    chunkLit x = do
      str <- Parser.Rule.textLit x
      pure (MkChunks [] str)

  builtin : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  builtin od = do
      name <- bounds $ Rule.builtin
      builtinTerm od name

  varTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  varTerm od = do
      name <- bounds $ identPart
      pure $ EVar (boundToFC od name) (val name) 0

  varAtTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  varAtTerm od = do
      name <- bounds $ identPart
      symbol "@"
      end <- bounds $ naturalLit
      pure $ EVar (mergeBounds (boundToFC od name) (boundToFC od end)) (val name) (cast $ val end)

  variable : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  variable od = varAtTerm od <|> varTerm od

  postFix : OriginDesc -> WithBounds RawExpr -> Grammar state (TokenRawToken) True (RawExpr)
  postFix od x = do
    tokenW $ symbol "."
    commit
    rightProject <|> leftProject
  where
    rightProject : Grammar state (TokenRawToken) True (RawExpr)
    rightProject = do
      e <- bounds $ (between (symbol "(") (symbol ")") $ exprTerm od)
      pure $ EProject (mergeBounds (boundToFC od x) (boundToFC od e)) (val x) (Right $ val e)
    leftProject : Grammar state (TokenRawToken) True (RawExpr)
    leftProject = do
      l <- bounds $ (between (symbol "{") (symbol "}") (sepBy (symbol ",") fieldName))
      pure $ EProject (mergeBounds (boundToFC od x) (boundToFC od l)) (val x) (Left $ map MkFieldName $ val l)
      {-
      pure $ case l of
           (MkBounded Nothing isIrrelevant bounds) =>
              EProject (mergeBounds (boundToFC od x) (boundToFC od l)) (val x) (Left $ [])
           (MkBounded (Just y) isIrrelevant bounds) =>
              EProject (mergeBounds (boundToFC od x) (boundToFC od l)) (val x) (Left $ forget $ y)
              -}

  atom : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  atom od = do
    builtin od <|> variable od
      <|> (textLit od) <|> emptyTextLit od
      <|> naturalLit od <|> integerLit od <|> doubleLit od
      <|> someLit od
      <|> piTermLong od
      <|> recordType od <|> recordLit od
      <|> union od
      <|> embed od
      <|> listLit od <|> (between (symbol "(") (symbol ")") $ exprTerm od)

  recordParser : OriginDesc
               -> Grammar state (TokenRawToken) True ()
               -> Grammar state (TokenRawToken) True ()
               -> (FC -> (SortedMap FieldName (RawExpr)) -> RawExpr)
               -> Grammar state (TokenRawToken) True (RawExpr)
  recordParser od sep empty cons = do
    start <- bounds $ tokenW $ symbol "{"
    commit
    let fc' = boundToFC od start
    emptyRecord fc' empty <|> populatedRecord fc'
  where
    emptyRecord : FC
                -> Grammar state (TokenRawToken) True ()
                -> Grammar state (TokenRawToken) True (RawExpr)
    emptyRecord fc empty = do
      end <- bounds empty
      pure $ cons (mergeBounds fc (boundToFC initBounds end)) $ SortedMap.fromList []
    recordField : Grammar state (TokenRawToken) True (FieldName, RawExpr)
    recordField = do
      i <- fieldName
      _ <- optional whitespace
      tokenW $ sep
      e <- exprTerm od
      pure (MkFieldName i, e)
    populatedRecord : FC -> Grammar state (TokenRawToken) True (RawExpr)
    populatedRecord fc = do
      es <- sepBy (tokenW $ symbol ",") recordField
      _ <- optional whitespace
      end <- bounds $ symbol "}"
      pure $ cons (mergeBounds fc (boundToFC od end)) $ SortedMap.fromList (es)

  recordType : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  recordType od = recordParser od (symbol ":") (symbol "}") ERecord

  recordLit : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  recordLit od = do
    start <- bounds $ tokenW $ symbol "{"
    commit
    let fc' = boundToFC od start
    emptyRecord fc' <|> populatedRecord fc'
  where
    emptyRecord : FC
                -> Grammar state (TokenRawToken) True (RawExpr)
    emptyRecord fc = do
      end <- bounds $ symbol "=" *> symbol "}"
      pure $ ERecordLit (mergeBounds fc (boundToFC initBounds end)) $ SortedMap.fromList []
    RecordElem : Type
    RecordElem = SortedMap FieldName (Expr ImportStatement)
    mkNestedRecord : List1 FieldName -> RawExpr -> RecordElem
    mkNestedRecord ks e =
      let (k ::: ks') = reverse ks in
      foldl (\ms,k' => fromList [(k', ERecordLit initFC ms)]) (fromList [(k, e)]) ks'
    dottedField : FC -> Grammar state (TokenRawToken) True RecordElem
    dottedField fc = do
      ls <- bounds dottedListRec
      symbol "="
      commit
      e <- exprTerm od
      pure $ mkNestedRecord (val ls) e
    punField : FC -> Grammar state (TokenRawToken) True RecordElem
    punField fc = do
      i <- bounds fieldName
      pure $ SortedMap.fromList [(MkFieldName (val i), EVar fc (val i) 0)] -- TODO check 0 here
    recordField : FC -> Grammar state (TokenRawToken) True RecordElem
    recordField fc = dottedField fc <|> punField fc
    populatedRecord : FC -> Grammar state (TokenRawToken) True (RawExpr)
    populatedRecord fc = do
      es <- sepBy1 (symbol ",") (recordField fc)
      end <- bounds $ symbol "}"
      pure $ ERecordLit (mergeBounds fc (boundToFC od end)) $ foldl1 (mergeWith (ECombine initFC)) es

  union : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  union od = do
    start <- bounds $ tokenW $ symbol "<"
    commit
    es <- sepBy (tokenW $ symbol "|") (unionComplex <|> unionSimple)
    _ <- optional whitespace
    end <- bounds $ symbol ">"
    pure $ EUnion (mergeBounds (boundToFC od start) (boundToFC od end)) $ SortedMap.fromList es
  where
    unionSimple : Grammar state (TokenRawToken) True (FieldName, Maybe (RawExpr))
    unionSimple = do
      name <- tokenW $ fieldName
      pure (MkFieldName name, Nothing)
    unionComplex : Grammar state (TokenRawToken) True (FieldName, Maybe (RawExpr))
    unionComplex = do
      name <- tokenW $ fieldName
      start <- bounds $ tokenW $ symbol ":"
      e <- exprTerm od
      _ <- optional whitespace
      pure (MkFieldName name, Just e)

  listLit : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  listLit od = do
    start <- bounds $ tokenW $ symbol "["
    commit
    let fc' = boundToFC od start
    (populatedList fc') <|> (emptyList fc')
  where
    listType : Grammar state (TokenRawToken) True (WithBounds RawExpr)
    listType = do
      tokenW $ symbol ":"
      bounds $ exprTerm od
    emptyList : FC -> Grammar state (TokenRawToken) True (RawExpr)
    emptyList fc = do
      tokenW $ symbol "]"
      ty <- listType
      pure $ EListLit (mergeBounds fc (boundToFC od ty)) (Just (val ty)) []
    populatedList : FC -> Grammar state (TokenRawToken) True (RawExpr)
    populatedList fc = do
      es <- sepBy1 (tokenW $ symbol ",") $ exprTerm od
      _ <- optional whitespace
      end <- bounds $ symbol "]"
      ty <- optional listType
      pure $ case ty of
                  Nothing =>
                    EListLit (mergeBounds fc (boundToFC od end)) Nothing (forget es)
                  (Just ty') =>
                    EListLit (mergeBounds fc (boundToFC initBounds ty')) (Just $ val ty') (forget es)

  opParser : Grammar state (TokenRawToken) True ()
           -> (FC -> RawExpr -> RawExpr -> RawExpr)
           -> Grammar state (TokenRawToken) True (RawExpr -> RawExpr -> RawExpr)
  opParser op cons = infixOp (do
      _ <- optional whitespace
      tokenW op) (boundedOp cons)

  mulOp : Grammar state (TokenRawToken) True (RawExpr -> RawExpr -> RawExpr)
  mulOp = (opParser (symbol "*") ENaturalTimes)

  withOp : Grammar state (TokenRawToken) True (RawExpr -> RawExpr -> RawExpr)
  withOp =
    do
      -- TODO find a better solution than just `match White` at the start of
      -- every operator
      _ <- optional $ whitespace
      tokenW $ keyword "with"
      commit
      dl <- dottedList
      _ <- optional $ whitespace
      tokenW $ symbol "="
      pure (boundedOp (with' dl))
  where
    with' : List1 FieldName -> FC -> Expr a -> Expr a -> Expr a
    with' xs fc x y = EWith fc x xs y

  projTermLeft : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  projTermLeft od = hchainl (fieldTerm od) projOp listFieldName
  where
    proj' : RawExpr -> WithBounds (List String) -> RawExpr
    proj' e ls =
      let start = getFC e
          end = boundToFC od ls
          fc' = mergeBounds start end
      in EProject fc' e $ Left $ map MkFieldName (val ls)
    projOp : Grammar state (TokenRawToken) True (RawExpr -> WithBounds (List String) -> RawExpr)
    projOp = do
      symbol ".{"
      commit
      pure proj'
    listFieldName : Grammar state (TokenRawToken) True (WithBounds (List String))
    listFieldName = do
      ls <- bounds $ (sepBy (symbol ",") fieldName) <* symbol "}"
      pure ls

  projTermRight : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  projTermRight od = hchainl (projTermLeft od) projOp (bounds $ exprTerm od <* symbol ")")
  where
    proj' : RawExpr -> WithBounds RawExpr -> RawExpr
    proj' e e' =
      let start = getFC e
          fc' = mergeBounds start (boundToFC od e')
      in EProject fc' e $ Right $ val e'
    projOp : Grammar state (TokenRawToken) True (RawExpr -> WithBounds RawExpr -> RawExpr)
    projOp = do
      symbol ".("
      commit
      pure proj'

  fieldTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  fieldTerm od = hchainl (atom od) fieldOp (bounds fieldName)
  where
    field' : RawExpr -> WithBounds String -> RawExpr
    field' e s =
      let start = getFC e
          end = boundToFC od $ s
          fc' = mergeBounds start end
      in EField fc' e (MkFieldName (val s))
    fieldOp : Grammar state (TokenRawToken) True (RawExpr -> WithBounds String -> RawExpr)
    fieldOp = do
      _ <- optional whitespace
      _ <- tokenW $ symbol "."
      pure $ field'

  appTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  appTerm od = (do
                x <- some $ projTermRight od
                pure $ List1.foldl1 (EApp EmptyFC) x) -- (appOp)

  mulTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  mulTerm od = chainl1 (appTerm od) (mulOp)

  boolTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  boolTerm od = chainl1 (mulTerm od) (boolOp)
  where
    boolOp : Grammar state (TokenRawToken) True (RawExpr -> RawExpr -> RawExpr)
    boolOp =
      (opParser (symbol "&&") EBoolAnd) <|> (opParser (symbol "||") EBoolOr)
      <|> (opParser (symbol "==") EBoolEQ) <|> (opParser (symbol "!=") EBoolNE)

  piTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  piTerm od = chainr1 (boolTerm od) (piOp)
  where
    epi' : String -> FC -> Expr a -> Expr a -> Expr a
    epi' n fc y z = EPi fc n y z
    piOp : Grammar state (TokenRawToken) True (RawExpr -> RawExpr -> RawExpr)
    piOp =
        infixOp (do
          _ <- optional whitespace
          arrow)
          (boundedOp $ epi' "_")

  annotTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  annotTerm od = chainr1 (piTerm od) (annotOp)
  where
    annotOp : Grammar state (TokenRawToken) True (RawExpr -> RawExpr -> RawExpr)
    annotOp = (opParser (symbol ":") EAnnot)

  plusTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  plusTerm od = chainl1 (annotTerm od) (plusOp)
  where
    plusOp : Grammar state (TokenRawToken) True (RawExpr -> RawExpr -> RawExpr)
    plusOp = (opParser (symbol "+") ENaturalPlus)

  otherTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  otherTerm od = chainl1 (annotTerm od) (otherOp)
  where
    otherOp : Grammar state (TokenRawToken) True (RawExpr -> RawExpr -> RawExpr)
    otherOp =
      (opParser (symbol "++") ETextAppend) <|> (opParser (symbol "#") EListAppend)
        <|> (opParser (symbol "&&") EBoolAnd) <|> (opParser (symbol "||") EBoolOr)
        <|> (opParser (symbol "==") EBoolEQ) <|> (opParser (symbol "!=") EBoolNE)
        <|> (opParser (symbol "+") ENaturalPlus)
        <|> (opParser (symbol "/\\" <|> symbol "∧") ECombine)
        <|> (opParser (symbol "//\\\\" <|> symbol "⩓") ECombineTypes)
        <|> (opParser (symbol "//" <|> symbol "⫽") EPrefer)
        <|> (opParser (symbol "::") ERecordCompletion)
        <|> (opParser (symbol "===" <|> symbol "≡") EEquivalent)
        <|> (opParser (symbol "?") EImportAlt)

  exprTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  exprTerm od = do
    piTermLong od <|>
    chainl1 (otherTerm od) (withOp) <|>
    letBinding od <|>
    lamTerm od <|>
    assertTerm od <|>
    ifTerm od <|>
    mergeTerm od <|>
    toMapTerm od

  letBinding : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  letBinding od = do
    start <- bounds $ tokenW $ keyword "let"
    commit
    name <- tokenW $ identPart
    ty <- optional (tokenW $ symbol ":" *> exprTerm od)
    _ <- tokenW $ symbol "="
    e <- bounds $ exprTerm od
    _ <- optional whitespace
    _ <- optional $ tokenW $ keyword "in"
    e' <- exprTerm od
    pure $ ELet (mergeBounds (boundToFC od start) (boundToFC od e)) name ty (val e) e'

  piTermLong : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  piTermLong od = do
    start <- bounds $ piStart
    commit
    name <- identPart
    _ <- symbol ":"
    t <- bounds $ exprTerm od
    _ <- symbol ")"
    _ <- arrow
    body <- bounds $ exprTerm od
    pure $ EPi (mergeBounds (boundToFC od start) (boundToFC od body))
            name (val t) (val body)
  where
    piStart : Grammar state (TokenRawToken) True ()
    piStart = ((symbol "∀" <|> keyword "forall") *> symbol "(")

  lamTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  lamTerm od = do
    start <- bounds $ lamStart
    commit
    name <- tokenW $ identPart
    _ <- symbol ":"
    _ <- optional whitespace
    t <- bounds $ exprTerm od
    _ <- tokenW $ symbol ")"
    _ <- arrow
    body <- bounds $ exprTerm od
    pure $ ELam (mergeBounds (boundToFC od start) (boundToFC od body))
            name (val t) (val body)
  where
    lamStart : Grammar state (TokenRawToken) True ()
    lamStart = tokenW $ ((symbol "\\" <|> symbol "λ") *> symbol "(")

  assertTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  assertTerm od = do
    start <- bounds $ tokenW $ keyword "assert"
    commit
    _ <- symbol ":"
    _ <- optional whitespace
    e <- bounds $ exprTerm od
    pure $ EAssert (mergeBounds (boundToFC od start) (boundToFC od e)) (val e)

  mergeTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  mergeTerm od = Text.Parser.Core.do
    start <- bounds $ tokenW $ keyword "merge"
    commit
    e1 <- bounds $ exprTerm od
    the (Grammar state TokenRawToken _ (RawExpr)) $
      case go (boundToFC od start) (val e1) of
           (Right x) => pure x
           (Left _) => fail "TODO implement better merge parse"
  where
    go : FC -> RawExpr -> Either () (RawExpr)
    go start (EApp fc x y) =
      pure $ EMerge (mergeBounds start fc) x y Nothing
    go start (EAnnot fc (EApp _ x y) t) =
      pure $ EMerge (mergeBounds start fc) x y (Just t)
    go _ _ = Left ()

  toMapTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  toMapTerm od = Text.Parser.Core.do
    start <- bounds $ tokenW $ keyword "toMap"
    commit
    e <- bounds $ exprTerm od
    pure $ case val e of -- TODO find out why pure must be here?
         (EAnnot fc x y) =>
            EToMap (mergeBounds (boundToFC od start) (boundToFC od e)) x (Just y)
         x =>
            EToMap (mergeBounds (boundToFC od start) (boundToFC od e)) x Nothing

  ifTerm : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
  ifTerm od = do
    start <- bounds $ tokenW $ keyword "if"
    commit
    i <- bounds $ exprTerm od
    _ <- optional whitespace
    _ <- bounds $ tokenW $ keyword "then"
    t <- bounds $ exprTerm od
    _ <- optional whitespace
    _ <- bounds $ tokenW $ keyword "else"
    e <- bounds $ exprTerm od
    pure $ EBoolIf (mergeBounds (boundToFC od start) (boundToFC od e))
            (val i) (val t) (val e)

finalParser : OriginDesc -> Grammar state (TokenRawToken) True (RawExpr)
finalParser od = do
  e <- exprTerm od
  -- _ <- optional $ many whitespace
  endOfInput
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

combineWhite : List (WithBounds TokenRawToken) -> List (WithBounds TokenRawToken)
combineWhite [] = []
combineWhite [x] = [x]
combineWhite (x :: y :: xs) =
  case (val x, val y) of
       (White, White) => combineWhite (y :: xs)
       (t, u) => x :: combineWhite (y :: xs)

doLex : String -> Either (StopReason, Int, Int, String) (List (WithBounds TokenRawToken))
doLex input = Idrall.Parser.Lexer.lex input

doParse' : OriginDesc -> List (WithBounds TokenRawToken) -> Either (List1 (ParsingError RawToken)) (RawExpr, List (WithBounds TokenRawToken))
doParse' od tokens =
  let processedTokens = (combineWhite . removeComments) tokens
  in parse (finalParser od) $ processedTokens

public export
parseExprNew : {default Nothing od : OriginDesc} -> String -> Either String (RawExpr, Int)
parseExprNew input = do
    Right tokens <- pure $ doLex input
      | Left e => Left $ show e

    Right (expr, x) <- pure $ doParse' od tokens
      | Left e => Left $ "\{show od} \{show e}"
    pure (expr, 0)

doParse : String -> IO ()
doParse input = do
  Right tokens <- pure $ doLex input
    | Left e => printLn $ show e
  putStrLn $ "tokens: " ++ show tokens

  let processedTokens = (combineWhite . removeComments) tokens
  putStrLn $ "processedTokens: " ++ show processedTokens
  Right (expr, x) <- pure $ doParse' Nothing tokens
    | Left e => printLn $ show e

  let doc = the (Doc (RawExpr)) $ pretty expr
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
