module Idrall.FC

import public Text.PrettyPrint.Prettyprinter

import Idrall.Path
import Idrall.Path

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
