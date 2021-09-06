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
import Debug.Trace

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

public export
data U = CType | Sort | Kind

export
Eq U where
  (==) CType CType = True
  (==) Sort Sort = True
  (==) Kind Kind = True
  (==) _ _ = False

export
Show U where
  show CType = "CType"
  show Sort = "Sort"
  show Kind = "Kind"

export
Pretty U where
  pretty CType = "Type"
  pretty Sort = "Sort"
  pretty Kind = "Kind"

mutual
  public export
  data Chunks a = MkChunks (List (String, Expr a)) String

  ||| Raw AST representation generated directly from the parser
  data Expr a
    = EConst FC U -- = EConst U
    | EVar FC String -- | EVar Name Int
    | ELam FC String (Expr a) (Expr a) -- | ELam Name (Expr a) (Expr a)
    | EPi FC String (Expr a) (Expr a) -- | EPi Name (Expr a) (Expr a)
    | EApp FC (Expr a) (Expr a) -- | EApp (Expr a) (Expr a)
    | ELet FC String (Expr a) (Expr a) -- | ELet Name (Maybe (Expr a)) (Expr a) (Expr a)
    | EAnnot FC (Expr a) (Expr a) -- | EAnnot (Expr a) (Expr a)
    | EBool FC -- | EBool
    | EBoolLit FC Bool -- | EBoolLit Bool
    | EBoolAnd FC (Expr a) (Expr a) -- | EBoolAnd (Expr a) (Expr a)
    | EBoolOr FC (Expr a) (Expr a) -- | EBoolOr  (Expr a) (Expr a)
    | EBoolEQ FC (Expr a) (Expr a) -- | EBoolEQ  (Expr a) (Expr a)
    | EBoolNE FC (Expr a) (Expr a) -- | EBoolNE  (Expr a) (Expr a)
    | EBoolIf FC (Expr a) (Expr a) (Expr a) -- | EBoolIf (Expr a) (Expr a) (Expr a)
    | ENatural FC -- | ENatural
    -- | ENaturalLit Nat
    | ENaturalFold FC -- | ENaturalFold
    | ENaturalBuild FC -- | ENaturalBuild
    | ENaturalIsZero FC -- | ENaturalIsZero
    | ENaturalEven FC -- | ENaturalEven
    | ENaturalOdd FC -- | ENaturalOdd
    | ENaturalToInteger FC -- | ENaturalToInteger
    | ENaturalSubtract FC -- | ENaturalSubtract
    | ENaturalShow FC -- | ENaturalShow
    | ENaturalPlus FC (Expr a) (Expr a) -- | ENaturalPlus (Expr a) (Expr a)
    | ENaturalTimes FC (Expr a) (Expr a) -- | ENaturalTimes (Expr a) (Expr a)
    | EInteger FC -- | EInteger
    -- | EIntegerLit Integer
    | EIntegerShow FC -- | EIntegerShow
    | EIntegerClamp FC -- | EIntegerClamp
    | EIntegerNegate FC -- | EIntegerNegate
    | EIntegerToDouble FC -- | EIntegerToDouble
    | EDouble FC -- | EDouble
    | EDoubleLit FC Double -- | EDoubleLit Double
    | EDoubleShow FC -- | EDoubleShow
    | EText FC -- | EText
    | ETextLit FC (Chunks a) -- | ETextLit (Chunks a)
    | ETextAppend FC (Expr a) (Expr a) -- | ETextAppend (Expr a) (Expr a)
    | ETextShow FC -- | ETextShow
    | ETextReplace FC -- | ETextReplace
    | EList FC -- | EList
    | EListLit FC (List (Expr a)) -- | EListLit (Maybe (Expr a)) (List (Expr a))
    | EListAppend FC (Expr a) (Expr a) -- | EListAppend (Expr a) (Expr a)
    | EListBuild FC -- | EListBuild
    | EListFold FC -- | EListFold
    | EListLength FC -- | EListLength
    | EListHead FC -- | EListHead
    | EListLast FC -- | EListLast
    | EListIndexed FC -- | EListIndexed
    | EListReverse FC -- | EListReverse
    | EOptional FC -- | EOptional
    | ENone FC -- | ENone
    | ESome FC (Expr a) -- | ESome (Expr a)
    | EEquivalent FC (Expr a) (Expr a) -- | EEquivalent (Expr a) (Expr a)
    | EAssert FC (Expr a) -- | EAssert (Expr a)
    | ERecord FC (SortedMap String (Expr a)) -- | ERecord (SortedMap FieldName (Expr a))
    | ERecordLit FC (SortedMap String (Expr a)) -- | ERecordLit (SortedMap FieldName (Expr a))
    | EUnion FC (SortedMap String (Maybe (Expr a))) -- | EUnion (SortedMap FieldName (Maybe (Expr a)))
    | ECombine FC (Expr a) (Expr a) -- | ECombine (Expr a) (Expr a)
    | ECombineTypes FC (Expr a) (Expr a) -- | ECombineTypes (Expr a) (Expr a)
    | EPrefer FC (Expr a) (Expr a) -- | EPrefer (Expr a) (Expr a)
    | ERecordCompletion FC (Expr a) (Expr a) -- | ERecordCompletion (Expr a) (Expr a)
    | EMerge FC (Expr a) (Expr a) (Maybe (Expr a)) -- | EMerge (Expr a) (Expr a) (Maybe (Expr a))
    -- | EToMap (Expr a) (Maybe (Expr a))
    | EField FC (Expr a) String -- | EField (Expr a) FieldName
    -- | EProject (Expr a) (Either (List FieldName) (Expr a))
    | EWith FC (Expr a) (List1 String) (Expr a) -- | EWith (Expr a) (List1 FieldName) (Expr a)
    -- | EImportAlt (Expr a) (Expr a)
    | EEmbed FC String -- | EEmbed (Import a)

mkExprFC : OriginDesc -> WithBounds x -> (FC -> x -> Expr a) -> Expr a
mkExprFC od e mkE = mkE (boundToFC od e) (val e)

mkExprFC0 : OriginDesc -> WithBounds x -> (FC -> Expr a) -> Expr a
mkExprFC0 od e mkE = mkE (boundToFC od e)

getBounds : Expr a -> FC
getBounds (EConst fc _) = fc
getBounds (EVar fc _) = fc
getBounds (ELam fc _ _ _) = fc
getBounds (EApp fc _ _) = fc
getBounds (EPi fc _ _ _) = fc
getBounds (ELet fc _ _ _) = fc
getBounds (EAnnot fc _ _) = fc
getBounds (EBool fc) = fc
getBounds (EBoolLit fc _) = fc
getBounds (EBoolAnd fc _ _) = fc
getBounds (EBoolOr fc _ _) = fc
getBounds (EBoolEQ fc _ _) = fc
getBounds (EBoolNE fc _ _) = fc
getBounds (EBoolIf fc _ _ _) = fc
getBounds (ENatural fc) = fc
getBounds (ENaturalBuild fc) = fc
getBounds (ENaturalFold fc) = fc
getBounds (ENaturalIsZero fc) = fc
getBounds (ENaturalEven fc) = fc
getBounds (ENaturalOdd fc) = fc
getBounds (ENaturalSubtract fc) = fc
getBounds (ENaturalToInteger fc) = fc
getBounds (ENaturalShow fc) = fc
getBounds (ENaturalPlus fc _ _) = fc
getBounds (ENaturalTimes fc _ _) = fc
getBounds (EInteger fc) = fc
getBounds (EIntegerShow fc) = fc
getBounds (EIntegerNegate fc) = fc
getBounds (EIntegerClamp fc) = fc
getBounds (EIntegerToDouble fc) = fc
getBounds (EDouble fc) = fc
getBounds (EDoubleLit fc _) = fc
getBounds (EDoubleShow fc) = fc
getBounds (EList fc) = fc
getBounds (EListLit fc _) = fc
getBounds (EListAppend fc _ _) = fc
getBounds (EListBuild fc) = fc
getBounds (EListFold fc) = fc
getBounds (EListLength fc) = fc
getBounds (EListHead fc) = fc
getBounds (EListLast fc) = fc
getBounds (EListIndexed fc) = fc
getBounds (EListReverse fc) = fc
getBounds (EText fc) = fc
getBounds (ETextAppend fc _ _) = fc
getBounds (ETextLit fc _) = fc
getBounds (ETextShow fc) = fc
getBounds (ETextReplace fc) = fc
getBounds (EOptional fc) = fc
getBounds (ESome fc _) = fc
getBounds (ENone fc) = fc
getBounds (EEquivalent fc _ _) = fc
getBounds (EAssert fc _) = fc
getBounds (ERecord fc _) = fc
getBounds (ERecordLit fc _) = fc
getBounds (EUnion fc _) = fc
getBounds (ECombine fc _ _) = fc
getBounds (ECombineTypes fc _ _) = fc
getBounds (EPrefer fc _ _) = fc
getBounds (ERecordCompletion fc _ _) = fc
getBounds (EMerge fc _ _ _) = fc
getBounds (EField fc _ _) = fc
getBounds (EWith fc _ _ _) = fc
getBounds (EEmbed fc _) = fc

updateBounds : FC -> Expr a -> Expr a
updateBounds fc (EConst _ z) = EConst fc z
updateBounds fc (EVar _ z) = EVar fc z
updateBounds fc (ELam _ z w v) = ELam fc z w v
updateBounds fc (EApp _ z w) = EApp fc z w
updateBounds fc (EPi _ n z w) = EPi fc n z w
updateBounds fc (ELet _ z w v) = ELet fc z w v
updateBounds fc (EAnnot _ z w) = EAnnot fc z w
updateBounds fc (EBool _) = EBool fc
updateBounds fc (EBoolLit _ z) = EBoolLit fc z
updateBounds fc (EBoolAnd _ z w) = EBoolAnd fc z w
updateBounds fc (EBoolOr _ z w) = EBoolOr fc z w
updateBounds fc (EBoolEQ _ z w) = EBoolEQ fc z w
updateBounds fc (EBoolNE _ z w) = EBoolNE fc z w
updateBounds fc (EBoolIf _ z w v) = EBoolIf fc z w v
updateBounds fc (ENatural _) = ENatural fc
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
updateBounds fc (EIntegerShow _) = EIntegerShow fc
updateBounds fc (EIntegerNegate _) = EIntegerNegate fc
updateBounds fc (EIntegerClamp _) = EIntegerClamp fc
updateBounds fc (EIntegerToDouble _) = EIntegerToDouble fc
updateBounds fc (EDouble _) = EDouble fc
updateBounds fc (EDoubleShow _) = EDoubleShow fc
updateBounds fc (EDoubleLit _ z) = EDoubleLit fc z
updateBounds fc (EList _) = EList fc
updateBounds fc (EListLit _ z) = EListLit fc z
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
    show (EConst fc x) = "(\{show fc}:EConst \{show x})"
    show (EVar fc x) = "(\{show fc}:EVar \{show x})"
    show (EApp fc x y) = "(\{show fc}:EApp \{show x} \{show y})"
    show (ELam fc n x y) = "(\{show fc}:ELam \{show n} \{show x} \{show y})"
    show (EPi fc n x y) = "(\{show fc}:EPi \{show n} \{show x} \{show y})"
    show (ELet fc x y z) = "(\{show fc}:ELet \{show x} \{show y} \{show z})"
    show (EAnnot fc x y) = "(\{show fc}:EAnnot \{show x} \{show y}"
    show (EBool fc) = "\{show fc}:EBool"
    show (EBoolLit fc x) = "\{show fc}:EBoolLit \{show x}"
    show (EBoolAnd fc x y) = "(\{show fc}:EBoolAnd \{show x} \{show y})"
    show (EBoolOr fc x y) = "\{show fc}:EBoolOr \{show x} \{show y})"
    show (EBoolEQ fc x y) = "\{show fc}:EBoolEQ \{show x} \{show y})"
    show (EBoolNE fc x y) = "\{show fc}:EBoolNE \{show x} \{show y})"
    show (EBoolIf fc x y z) = "\{show fc}:EBoolIf \{show x} \{show y}) \{show z})"
    show (ENatural fc) = "\{show fc}:ENatural"
    show (ENaturalBuild fc) = "(\{show fc}:ENaturalBuild)"
    show (ENaturalFold fc) = "(\{show fc}:ENaturalFold)"
    show (ENaturalIsZero fc) = "(\{show fc}:ENaturalZero)"
    show (ENaturalEven fc) = "(\{show fc}:ENaturalEven)"
    show (ENaturalOdd fc) = "(\{show fc}:ENaturalOdd)"
    show (ENaturalSubtract fc) = "(\{show fc}:ENaturalSubtract)"
    show (ENaturalToInteger fc) = "(\{show fc}:ENaturalToInteger)"
    show (ENaturalShow fc) = "(\{show fc}:ENaturalShow)"
    show (ENaturalPlus fc x y) = "\{show fc}:ENaturalPlus \{show x} \{show y})"
    show (ENaturalTimes fc x y) = "\{show fc}:ENaturalTimes \{show x} \{show y})"
    show (EInteger fc) = "\{show fc}:EInteger"
    show (EIntegerShow fc) = "(\{show fc}:EIntegerShow)"
    show (EIntegerNegate fc) = "(\{show fc}:EIntegerNegate)"
    show (EIntegerClamp fc) = "(\{show fc}:EIntegerClamp)"
    show (EIntegerToDouble fc) = "(\{show fc}:EIntegerToDouble)"
    show (EDouble fc) = "\{show fc}:EDouble"
    show (EDoubleLit fc x) = "(\{show fc}:EDoubleLit \{show x})"
    show (EDoubleShow fc) = "(\{show fc}:EDoubleShow)"
    show (EList fc) = "(\{show fc}:EList)"
    show (EListLit fc x) = "(\{show fc}:EListLit \{show x})"
    show (EListAppend fc x y) = "(\{show fc}:EListAppend \{show x} \{show y})"
    show (EListBuild fc) = "(\{show fc}:EListBuild)"
    show (EListFold fc) = "(\{show fc}:EListFold)"
    show (EListLength fc) = "(\{show fc}:EListLength)"
    show (EListHead fc) = "(\{show fc}:EListHead)"
    show (EListLast fc) = "(\{show fc}:EListLast)"
    show (EListIndexed fc) = "(\{show fc}:EListIndexed)"
    show (EListReverse fc) = "(\{show fc}:EListReverse)"
    show (EText fc) = "(\{show fc}:ETextLit"
    show (ETextLit fc cs) = "(\{show fc}:ETextLit \{show cs}"
    show (ETextAppend fc x y) = "(\{show fc}:ETextAppend \{show x} \{show y}"
    show (ETextShow fc) = "(\{show fc}:ETextShow)"
    show (ETextReplace fc) = "(\{show fc}:ETextReplace)"
    show (EOptional fc) = "(\{show fc}:EOptional)"
    show (ESome fc x) = "(\{show fc}:ESome \{show x})"
    show (ENone fc) = "(\{show fc}:ENone)"
    show (EField fc x s) = "(\{show fc}:EField \{show x} \{show s}"
    show (EWith fc x s y) = "(\{show fc}:EWith \{show x} \{show s} \{show y})"
    show (EEquivalent fc x y) = "(\{show fc}:EEquivalent \{show x} \{show y}"
    show (EAssert fc x) = "(\{show fc}:EAssert \{show x}"
    show (ERecord fc x) = "(\{show fc}:ERecord \{show x}"
    show (ERecordLit fc x) = "(\{show fc}:ERecordLit \{show x}"
    show (EUnion fc x) = "(\{show fc}:EUnion \{show x}"
    show (ECombine fc x y) = "(\{show fc}:ECombine \{show x} \{show y}"
    show (ECombineTypes fc x y) = "(\{show fc}:ECombineTypes \{show x} \{show y}"
    show (EPrefer fc x y) = "(\{show fc}:EPrefer \{show x} \{show y}"
    show (ERecordCompletion fc x y) = "(\{show fc}:ERecordCompletion \{show x} \{show y}"
    show (EMerge fc x y z) = "(\{show fc}:EMerge \{show x} \{show y} \{show z}"
    show (EEmbed fc x) = "(\{show fc}:EEmbed \{show fc} \{show x})"

prettyDottedList : List String -> Doc ann
prettyDottedList [] = pretty ""
prettyDottedList (x :: []) = pretty x
prettyDottedList (x :: xs) = pretty x <+> pretty "." <+> prettyDottedList xs

mutual
  prettySortedMap : Pretty x
                  => (Doc ann -> Doc ann)
                  -> Doc ann
                  -> (SortedMap String x)
                  -> Doc ann
  prettySortedMap wrapping sign e =
    let ls = SortedMap.toList e
        lsDoc = map (go sign) ls
    in
    wrapping $ foldl (<++>) neutral (punctuate comma lsDoc)
  where
    go : Doc ann -> (String, x) -> Doc ann
    go x (s, e) = pretty s <++> x <++> pretty e

  prettyUnion : Pretty x
              => (SortedMap String (Maybe x))
              -> Doc ann
  prettyUnion e =
    let ls = SortedMap.toList e
        lsDoc = map go ls
    in
    enclose langle (space <+> rangle) $ foldl (<++>) neutral (punctuate (space <+> pipe) lsDoc)
  where
    go : (String, Maybe x) -> Doc ann
    go (s, Nothing) = pretty s
    go (s, Just e) = pretty s <++> colon <++> pretty e

  Pretty (Chunks ()) where
    pretty (MkChunks xs x) = pretty xs <+> pretty x

  Pretty (Expr ()) where
    pretty (EConst fc x) = pretty x
    pretty (EVar fc x) = pretty x
    pretty (EApp fc x y) = pretty x <++> pretty y
    pretty (ELam fc n x y) =
      pretty "\\" <+> parens (pretty n <++> colon <++> pretty x)
        <++> pretty "->" <++> pretty y
    pretty (EPi fc "_" x y) = pretty x <++> pretty "->" <++> pretty y
    pretty (EPi fc n x y) =
      pretty "forall" <+> parens (pretty n <++> colon <++> pretty x)
        <++> pretty "->" <++> pretty y
    pretty (ELet fc x y z) =
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
    pretty (EIntegerShow fc) = pretty "Integer/show"
    pretty (EIntegerNegate fc) = pretty "Integer/negate"
    pretty (EIntegerClamp fc) = pretty "Integer/clamp"
    pretty (EIntegerToDouble fc) = pretty "Integer/toDouble"
    pretty (EDouble fc) = pretty "Double"
    pretty (EDoubleLit fc x) = pretty $ show x
    pretty (EDoubleShow fc) = pretty "Double/show"
    pretty (EList fc) = pretty "List"
    pretty (EListLit fc xs) = pretty xs
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
  let xB = getBounds x
      yB = getBounds y
      mB = mergeBounds xB yB in
      op mB x y

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
     "Optional" => pure $ cons EOptional
     "None" => pure $ cons ENone
     "NaN" => pure $ EDoubleLit (boundToFC initBounds str) (0.0/0.0)
     "True" => pure $ EBoolLit (boundToFC initBounds str) True
     "False" => pure $ EBoolLit (boundToFC initBounds str) False
     "Bool" => pure $ EBool (boundToFC initBounds str)
     "Text" => pure $ EText (boundToFC initBounds str)
     "Natural" => pure $ ENatural (boundToFC initBounds str)
     "Integer" => pure $ EInteger (boundToFC initBounds str)
     "Double" => pure $ EDouble (boundToFC initBounds str)
     "Type" => pure $ EConst (boundToFC initBounds str) CType
     "Kind" => pure $ EConst (boundToFC initBounds str) Kind
     "Sort" => pure $ EConst (boundToFC initBounds str) Sort
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

  someLit : Grammar state (TokenRawToken) True (Expr ())
  someLit = do
    start <- bounds $ tokenW $ someBuiltin
    e <- bounds $ exprTerm
    pure $ ESome (mergeBounds (boundToFC initBounds start) (boundToFC initBounds e)) $ val e

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

  builtin : Grammar state (TokenRawToken) True (Expr ())
  builtin = do
      name <- bounds $ Rule.builtin
      builtinTerm name

  varTerm : Grammar state (TokenRawToken) True (Expr ())
  varTerm = do
      name <- bounds $ identPart
      pure $ EVar (boundToFC initBounds name) $ val name

  atom : Grammar state (TokenRawToken) True (Expr ())
  atom = do
    a <- builtin <|> varTerm <|> textLit
      <|> doubleLit
      <|> someLit
      <|> recordType <|> recordLit
      <|> union
      <|> embed
      <|> listLit <|> (between (symbol "(") (symbol ")") exprTerm)
    pure a

  recordParser : Grammar state (TokenRawToken) True ()
               -> (FC -> (SortedMap String (Expr ())) -> Expr ())
               -> Grammar state (TokenRawToken) True (Expr ())
  recordParser sep cons = do
    start <- bounds $ tokenW $ symbol "{"
    commit
    let fc = boundToFC initBounds start
    emptyRecord fc <|> populatedRecord fc
  where
    emptyRecord : FC -> Grammar state (TokenRawToken) True (Expr ())
    emptyRecord fc = do
      end <- bounds $ symbol "}"
      pure $ cons (mergeBounds fc (boundToFC initBounds end)) $ SortedMap.fromList []
    recordField : Grammar state (TokenRawToken) True (String, Expr ())
    recordField = do
      i <- identPart
      _ <- optional whitespace
      tokenW $ sep
      e <- exprTerm
      pure (i, e)
    populatedRecord : FC -> Grammar state (TokenRawToken) True (Expr ())
    populatedRecord fc = do
      es <- sepBy (tokenW $ symbol ",") recordField
      end <- bounds $ symbol "}"
      pure $ cons (mergeBounds fc (boundToFC initBounds end)) $ SortedMap.fromList (es)

  recordType : Grammar state (TokenRawToken) True (Expr ())
  recordType = recordParser (symbol ":") ERecord

  recordLit : Grammar state (TokenRawToken) True (Expr ())
  recordLit = recordParser (symbol "=") ERecordLit

  union : Grammar state (TokenRawToken) True (Expr ())
  union = do
    start <- bounds $ tokenW $ symbol "<"
    commit
    es <- sepBy (tokenW $ symbol "|") (unionComplex <|> unionSimple)
    end <- bounds $ tokenW $ symbol ">"
    pure $ EUnion (mergeBounds (boundToFC initBounds start) (boundToFC initBounds end)) $ SortedMap.fromList es
  where
    unionSimple : Grammar state (TokenRawToken) True (String, Maybe (Expr ()))
    unionSimple = do
      name <- tokenW $ identPart
      pure (name, Nothing)
    unionComplex : Grammar state (TokenRawToken) True (String, Maybe (Expr ()))
    unionComplex = do
      name <- tokenW $ identPart
      start <- bounds $ tokenW $ symbol ":"
      e <- exprTerm
      _ <- optional whitespace
      pure (name, Just e)

  listLit : Grammar state (TokenRawToken) True (Expr ())
  listLit = do
    start <- bounds $ tokenW $ symbol "["
    commit
    let fc = boundToFC initBounds start
    (populatedList fc) <|> (emptyList fc)
  where
    emptyList : FC -> Grammar state (TokenRawToken) True (Expr ())
    emptyList fc = do
      end <- bounds $ symbol "]"
      pure $ EListLit (mergeBounds fc (boundToFC initBounds end)) []
    populatedList : FC -> Grammar state (TokenRawToken) True (Expr ())
    populatedList fc = do
      es <- sepBy1 (tokenW $ symbol ",") exprTerm
      end <- bounds $ symbol "]"
      pure $ EListLit (mergeBounds fc (boundToFC initBounds end)) (forget es)

  opParser : String
     -> (FC -> Expr () -> Expr () -> Expr ())
     -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
  opParser op cons = infixOp (do
      _ <- optional whitespace
      tokenW $ symbol op) (boundedOp cons)

  otherOp : FC -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
  otherOp fc =
    (opParser "++" ETextAppend) <|> (opParser "#" EListAppend)
      <|> (opParser "/\\" ECombine) <|> (opParser "//\\\\" ECombineTypes)
      <|> (opParser "//" EPrefer) <|> (opParser "::" ERecordCompletion)
      <|> (opParser "===" EEquivalent)

  plusOp : FC -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
  plusOp fc = (opParser "+" ENaturalPlus)

  mulOp : FC -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
  mulOp fc = (opParser "*" ENaturalTimes)

  boolOp : FC -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
  boolOp fc =
    (opParser "&&" EBoolAnd) <|> (opParser "||" EBoolOr)
    <|> (opParser "==" EBoolEQ) <|> (opParser "!=" EBoolNE)

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
  appOp fc = (opParser ":" EAnnot) <|> infixOp whitespace (boundedOp EApp)

  withOp : FC -> Grammar state (TokenRawToken) True (Expr () -> Expr () -> Expr ())
  withOp fc =
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
    with' : List1 String -> FC -> Expr a -> Expr a -> Expr a
    with' xs fc x y = EWith fc x xs y

  otherTerm : Grammar state (TokenRawToken) True (Expr ())
  otherTerm = chainl1 atom (otherOp EmptyFC)

  mulTerm : Grammar state (TokenRawToken) True (Expr ())
  mulTerm = chainl1 otherTerm (mulOp EmptyFC)

  plusTerm : Grammar state (TokenRawToken) True (Expr ())
  plusTerm = chainl1 mulTerm (plusOp EmptyFC)

  boolTerm : Grammar state (TokenRawToken) True (Expr ())
  boolTerm = chainl1 plusTerm (boolOp EmptyFC)

  piTerm : Grammar state (TokenRawToken) True (Expr ())
  piTerm = chainr1 boolTerm (piOp EmptyFC)

  fieldTerm : Grammar state (TokenRawToken) True (Expr ())
  fieldTerm = hchainl piTerm fieldOp (bounds identPart)
  where
    field' : Expr () -> WithBounds String -> Expr ()
    field' e s =
      let start = getBounds e
          end = boundToFC initBounds $ s
          fc' = mergeBounds start end
      in EField fc' e (val s)
    fieldOp : Grammar state (TokenRawToken) True (Expr () -> WithBounds String -> Expr ())
    fieldOp = do
      _ <- optional whitespace
      _ <- tokenW $ symbol "."
      pure $ field'

  appTerm : Grammar state (TokenRawToken) True (Expr ())
  appTerm = chainl1 fieldTerm (appOp EmptyFC)

  exprTerm : Grammar state (TokenRawToken) True (Expr ())
  exprTerm = do
    letBinding <|>
    lamTerm <|>
    assertTerm <|>
    ifTerm <|>
    mergeTerm <|>
    chainl1 appTerm (withOp EmptyFC)

  letBinding : Grammar state (TokenRawToken) True (Expr ())
  letBinding = do
    start <- bounds $ tokenW $ keyword "let"
    commit
    name <- tokenW $ identPart
    _ <- tokenW $ symbol "="
    e <- exprTerm
    _ <- whitespace
    end <- bounds $ tokenW $ keyword "in" -- TODO is this a good end position?
    e' <- exprTerm
    pure $ ELet (mergeBounds (boundToFC initBounds start) (boundToFC initBounds end)) name e e'

  lamTerm : Grammar state (TokenRawToken) True (Expr ())
  lamTerm = do
    start <- bounds $ tokenW $ (do symbol "\\" ; symbol "(")
    commit
    name <- tokenW $ identPart
    _ <- symbol ":"
    _ <- whitespace
    t <- bounds $ exprTerm
    _ <- tokenW $ symbol ")"
    _ <- tokenW $ symbol "->"
    body <- bounds $ exprTerm
    pure $ ELam (mergeBounds (boundToFC initBounds start) (boundToFC initBounds body))
            name (val t) (val body)

  assertTerm : Grammar state (TokenRawToken) True (Expr ())
  assertTerm = do
    start <- bounds $ tokenW $ keyword "assert"
    commit
    _ <- symbol ":"
    _ <- whitespace
    e <- bounds $ exprTerm
    pure $ EAssert (mergeBounds (boundToFC initBounds start) (boundToFC initBounds e)) (val e)

  mergeTerm : Grammar state (TokenRawToken) True (Expr ())
  mergeTerm = Text.Parser.Core.do
    start <- bounds $ tokenW $ keyword "merge"
    commit
    e1 <- bounds exprTerm
    the (Grammar state TokenRawToken _ (Expr ())) $
      case go (boundToFC initBounds start) (val e1) of
           (Right x) => pure x
           (Left _) => fail "TODO implement better merge parse"
  where
    go : FC -> Expr () -> Either () (Expr ())
    go start (EApp fc x y) =
      pure $ EMerge (mergeBounds start fc) x y Nothing
    go start (EAnnot fc (EApp _ x y) t) =
      pure $ EMerge (mergeBounds start fc) x y (Just t)
    go _ _ = Left ()

  ifTerm : Grammar state (TokenRawToken) True (Expr ())
  ifTerm = do
    start <- bounds $ tokenW $ keyword "if"
    commit
    i <- bounds $ exprTerm
    _ <- whitespace
    _ <- bounds $ tokenW $ keyword "then"
    t <- bounds $ exprTerm
    _ <- whitespace
    _ <- bounds $ tokenW $ keyword "else"
    e <- bounds $ exprTerm
    pure $ EBoolIf (mergeBounds (boundToFC initBounds start) (boundToFC initBounds e))
            (val i) (val t) (val e)

finalParser : Grammar state (TokenRawToken) True (Expr ())
finalParser = do
  e <- exprTerm
  _ <- optional $ many whitespace
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

doParse : String -> IO ()
doParse input = do
  Right tokens <- pure $ Idrall.Parser.Lexer.lex input
    | Left e => printLn $ show e
  putStrLn $ "tokens: " ++ show tokens

  Right (expr, x) <- pure $ parse finalParser tokens -- TODO use finalParser
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
