module Idrall.FC

import public Text.PrettyPrint.Prettyprinter

import Idrall.Path

import Data.String
import Data.List
import System.File

public export
FilePos : Type
FilePos = (Nat, Nat)

-- does fancy stuff for idris, for now it can just be a Maybe filename
public export
OriginDesc : Type
OriginDesc = Maybe String

-- TODO use this as a Maybe for MkVirtualFC
data FCDetails = MkFCDetails OriginDesc FilePos FilePos

public export
data FC = MkFC        OriginDesc FilePos FilePos
        | ||| Virtual FCs are FC attached to desugared/generated code.
          MkVirtualFC OriginDesc FilePos FilePos
        | EmptyFC
%name FC fc

public export
interface HasFC a where
  constructor MkHasFC
  getFC : a -> FC

public export
Show FC where
  show (MkFC Nothing x y) = "\{show x}-\{show y}"
  show (MkFC (Just s) x y) = "\{s}:\{show x}-\{show y}"
  show (MkVirtualFC x y z) = "MkVirtualFCTODO"
  show EmptyFC = ""

prettyPairs : (Nat, Nat) -> (Nat, Nat) -> Doc ann
prettyPairs x y = pretty (show x) <++> pretty "->" <++> pretty (show y)

public export
Pretty FC where
  pretty (MkFC Nothing y z) = prettyPairs y z
  pretty (MkFC (Just x) y z) = pretty x <++> softline <+> prettyPairs y z
  pretty (MkVirtualFC Nothing y z) = prettyPairs y z
  pretty (MkVirtualFC (Just x) y z) = pretty "Virtual File" <++> pretty x <++> softline <+> prettyPairs y z
  pretty EmptyFC = neutral

public export
initFC : FC
initFC = EmptyFC

public export
originFromFC : FC -> OriginDesc
originFromFC (MkFC x y z) = x
originFromFC (MkVirtualFC x y z) = x
originFromFC EmptyFC = Nothing

export
fcToVFC : FC -> FC
fcToVFC (MkFC x y z) = MkVirtualFC x y z
fcToVFC fc@(MkVirtualFC x y z) = fc
fcToVFC EmptyFC = EmptyFC

ex1 : String
ex1 = """
1 some text
2 another line that's a bit longer
3 again stuff
"""

printArrows : Nat -> (Nat, Nat) -> (Nat, Nat) -> String
printArrows max (ln, col) (ln', col') =
  case (ln <= ln', col <= col') of
       (True, True) =>
          let pad = replicate col ' '
              end = if col' > max then max else col'
              add1 = if (ln == ln' && col == col') then 1 else 0
              arrowCount = (minus end col) + add1
              -- the 1 is for if the span starts and ends on a single char
              arrows = replicate arrowCount '^'
          in pack $ pad ++ arrows
       _ => "^-^-^"

safePrint : List String -> (Nat, Nat) -> (Nat, Nat) -> Maybe String
safePrint xs s@(ln, col) e@(ln', col') =
  case Data.List.inBounds ln xs of
       (Yes prf) =>
          let str = index ln xs
              lineNoPrefix = show ln ++ "| "
              whitePrefix = pack $ List.replicate (length lineNoPrefix) ' '
              in
              Just $ unlines [lineNoPrefix ++ str, whitePrefix ++ printArrows (length str) s e]
       (No contra) => neutral -- TODO better failure case

formatSpanSnippet : FC -> String -> Maybe String
formatSpanSnippet fc str =
  let ls = lines str
      startpos' = startpos fc
      endpos' = endpos fc
      neutralpos = (0,0)
      in
  case (startpos', endpos') of
       ((Just s), (Just e)) => safePrint ls s e
       ((Just s), Nothing) => safePrint ls s neutralpos
       (Nothing, (Just e)) => safePrint ls neutralpos e
       (Nothing, Nothing) => neutral
where
  startpos : FC -> Maybe (Nat, Nat)
  startpos (MkFC x start _) = Just start
  startpos (MkVirtualFC x start _) = Just start
  startpos EmptyFC = Nothing
  endpos : FC -> Maybe (Nat, Nat)
  endpos (MkFC x _ end) = Just end
  endpos (MkVirtualFC x _ end) = Just end
  endpos EmptyFC = Nothing

export
getSpanSnippet : FC -> IO (Maybe String)
getSpanSnippet fc@(MkFC (Just x) start end) = do
  Right str <- readFile x | Left e => pure neutral
  pure $ formatSpanSnippet fc str
getSpanSnippet fc@(MkVirtualFC (Just x) start end) = do
  Right str <- readFile x | Left e => pure neutral
  pure $ formatSpanSnippet fc str
getSpanSnippet (MkFC Nothing y z) = pure neutral
getSpanSnippet (MkVirtualFC Nothing y z) = pure neutral
getSpanSnippet EmptyFC = pure neutral

doPrint : String -> (Nat, Nat) -> (Nat, Nat) -> IO ()
doPrint path start end =
  let fc = MkFC (Just path) start end
      str = getSpanSnippet fc
  in
  case !str of
       Nothing => putStrLn "error"
       (Just x) => putStrLn x
