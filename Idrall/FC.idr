module Idrall.FC

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

public export
initFC : FC
initFC = EmptyFC

