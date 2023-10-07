module Idrall.Derive.Common

import Language.Reflection
import Data.List1
import public Data.String

%language ElabReflection

%hide Data.List.lookup

---------------------------------------------------
-- from idris2-elab-util Language.Reflection.Syntax
---------------------------------------------------

||| Named type.
|||
||| This is an alias for `MkTyp EmptyFC`.
export
mkTy : (n : Name) -> (ty : TTImp) -> ITy
mkTy = MkTy EmptyFC EmptyFC

||| Creates a variable from the given name
|||
||| Names are best created using quotes: `{ AName },
||| `{ In.Namespacs.Name }.
|||
||| Likewise, if the name is already known at the time of
||| writing, use quotes for defining variables directly: `(AName)
export
var : Name -> TTImp
var = IVar EmptyFC

public export
FromString Name where
  fromString s = run (split ('.' ==) s) []
    where run : List1 String -> List String -> Name
          run (h ::: []) []        = UN $ Basic h
          run (h ::: []) ns        = NS (MkNS ns) (UN $ Basic h)
          run (h ::: (y :: ys)) xs = run (y ::: ys) (h :: xs)

||| Alias for `var . fromString`
export
varStr : String -> TTImp
varStr = var . fromString

||| A pattern clause consisting of the left-hand and
||| right-hand side of the pattern arrow "=>".
|||
||| This is an alias for `PatClause EmptyFC`.
export
patClause : (lhs : TTImp) -> (rhs : TTImp) -> Clause
patClause = PatClause EmptyFC
------

||| from idris2-lsp
export
stripNs : Name -> Name
stripNs (NS _ x) = x
stripNs x = x

||| from idris2-lsp
covering
export
genReadableSym : String -> Elab Name
genReadableSym hint = do
  MN v i <- genSym hint
    | _ => fail "cannot generate readable argument name"
  pure $ UN $ Basic (v ++ show i)

||| from idris2-lsp
export
primStr : String -> TTImp
primStr = IPrimVal EmptyFC . Str

||| from idris2-lsp
export
bindvar : String -> TTImp
bindvar = IBindVar EmptyFC

||| from idris2-lsp
export
implicit' : TTImp
implicit' = Implicit EmptyFC True

||| moved from where clause
export
getArgs : TTImp -> Elab (List (Name, TTImp))
getArgs (IPi _ _ _ (Just n) argTy retTy) = ((n, argTy) ::) <$> getArgs retTy
getArgs (IPi _ _ _ Nothing _ _) = fail $ "All arguments must be explicitly named"
getArgs _ = pure []

public export
Cons : Type
Cons = (List (Name, List (Name, TTImp)))

export
logCons : Cons -> Elab ()
logCons [] = do
  pure ()
logCons (x :: xs) = do
  more x
  logCons xs
where
  go : List (Name, TTImp) -> Elab ()
  go [] =  pure ()
  go ((n, t) :: ys) = do
    logMsg "" 7 ("ArgName: " ++ show n)
    logTerm "" 7 "ArgType" t
    go ys
  more : (Name, List (Name, TTImp)) -> Elab ()
  more (constructor', args) = do
    logMsg "" 7 ("Constructor: " ++ show constructor')
    go args

||| Used with FromDhall interface, to dervice implementations
||| for ADTs or Records
public export
data IdrisType
  = ADT
  | Record

public export
record Options where
  constructor MkOptions
  ||| This function is used to adjust constructor argument names
  ||| during encoding and decoding
  fieldNameModifier          : String -> String

export
defaultOptions : Options
defaultOptions = MkOptions id

