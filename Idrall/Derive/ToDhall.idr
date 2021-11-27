module Idrall.Derive.ToDhall

import Idrall.Expr
import Idrall.Error
import Idrall.Pretty
import Idrall.Derive.Common

import public Data.SortedMap

import Language.Reflection

%language ElabReflection

%hide Idrall.Expr.Name
%hide Data.List.lookup

public export
interface ToDhall ty where
  toDhallType : Expr Void
  toDhall : ty -> Expr Void

export
ToDhall Nat where
  toDhallType = ENatural EmptyFC
  toDhall x = ENaturalLit EmptyFC x

export
ToDhall Bool where
  toDhallType = EBool EmptyFC
  toDhall x = EBoolLit EmptyFC x

export
ToDhall Integer where
  toDhallType = EInteger EmptyFC
  toDhall x = EIntegerLit EmptyFC x

export
ToDhall Double where
  toDhallType = EDouble EmptyFC
  toDhall x = EDoubleLit EmptyFC x

export
ToDhall String where
  toDhallType = EText EmptyFC
  toDhall x = ETextLit EmptyFC (MkChunks [] x)

export
ToDhall ty => ToDhall (List ty) where
  toDhallType = EApp EmptyFC (EList EmptyFC) (toDhallType {ty=ty})
  toDhall xs = EListLit EmptyFC (Just (toDhallType {ty=ty})) (map toDhall xs)

export
ToDhall ty => ToDhall (Maybe ty) where
  toDhallType = EApp EmptyFC (EOptional EmptyFC) (toDhallType {ty=ty})
  toDhall Nothing = EApp EmptyFC (ENone EmptyFC) (toDhallType {ty=ty})
  toDhall (Just x) = ESome EmptyFC (toDhall x)

export
Pretty Void where
  pretty x = pretty ""

-- Record Type functions
-- given a idris Record constructor arg in the form (Name, type),
-- return a dhall record field for use in the ERecord constructor.
argToFieldType : List (Name, TTImp) -> TTImp
argToFieldType [] = `([])
argToFieldType ((n, t) :: xs) =
  let name = primStr $ (show n)
  in `(MkPair (MkFieldName ~name) (toDhallType {ty = ~t}) :: ~(argToFieldType xs))

dhallRecTypeFromRecArg : List (Name, TTImp) -> TTImp
dhallRecTypeFromRecArg xs =
  `(ERecord EmptyFC $ fromList $ ~(argToFieldType xs))

genRecordTypeClauses : -- IdrisType ->
             Name -> Name -> Cons -> List Clause
genRecordTypeClauses funName arg [] = do
  pure $ patClause `(~(var funName)) (dhallRecTypeFromRecArg [])
genRecordTypeClauses funName arg ((n, ls) :: xs) = do
  pure $ patClause `(~(var funName)) (dhallRecTypeFromRecArg ls)

-- Record Lit functions
argToField : Name -> List (Name, TTImp) -> TTImp
argToField arg [] = `([])
argToField arg ((n, _) :: xs) =
  let name = primStr $ (show n)
  in `(MkPair (MkFieldName ~name) (toDhall (~(var n) ~(var arg))) :: ~(argToField arg xs))

dhallRecLitFromRecArg : Name -> List (Name, TTImp) -> TTImp
dhallRecLitFromRecArg arg xs =
  `(ERecordLit EmptyFC $ fromList $ ~(argToField arg xs))

genRecordLitClauses : -- IdrisType ->
             Name -> Name -> Cons -> List Clause
genRecordLitClauses funName arg [] = do
  pure $ patClause `(~(var funName) ~(bindvar $ show arg)) (dhallRecLitFromRecArg arg [])
genRecordLitClauses funName arg ((n, ls) :: xs) = do
  pure $ patClause `(~(var funName) ~(bindvar $ show arg)) (dhallRecLitFromRecArg arg ls)

export
deriveToDhall : -- IdrisType ->
                  (name : Name) -> Elab ()
deriveToDhall n = do
  logMsg "" 0 ("yesss")
  [(name, _)] <- getType n
          | _ => fail "Ambiguous name"
  let funNameType = UN $ Basic ("toDhallType" ++ show (stripNs name))
  let funNameLit = UN $ Basic ("toDhallLit" ++ show (stripNs name))
  let objName = UN $ Basic ("__impl_toDhall" ++ show (stripNs name))

  conNames <- getCons name

  -- get the constructors of the record
  -- cons : (List (Name, List (Name, TTImp)))
  cons <- for conNames $ \n => do
    [(conName, conImpl)] <- getType n
      | _ => fail $ show n ++ "constructor must be in scope and unique"
    args <- getArgs conImpl
    pure (conName, args)

  logCons cons

  argName <- genReadableSym "arg"

  -- clauses <- genClauses funName argName cons
  let funClaimType = IClaim EmptyFC MW Export [Inline] (MkTy EmptyFC EmptyFC funNameType `(Expr Void))
  -- add a catch all pattern
  let funDeclType = IDef EmptyFC funNameType $ (genRecordTypeClauses funNameType argName cons)
  -- declare the fuction in the env
  declare [funClaimType, funDeclType]

  let funClaimLit = IClaim EmptyFC MW Export [Inline] (MkTy EmptyFC EmptyFC funNameLit `(~(var name) -> Expr Void))
  let funDeclLit = IDef EmptyFC funNameLit $ (genRecordLitClauses funNameLit argName cons)
  declare [funClaimLit, funDeclLit]

  declare []

-- Record example
record ExRec1 where
  constructor MkExRec1
  mn : Maybe Nat
  st : String

%runElab (deriveToDhall `{ ExRec1 })

type :  TTImp
type = IType EmptyFC

iData :  Visibility
      -> Name
      -> (tycon : TTImp)
      -> (opts  : List DataOpt)
      -> (cons  : List ITy)
      -> Decl
iData v n tycon opts cons = IData EmptyFC v (MkData EmptyFC n tycon opts cons)

simpleData : Visibility -> Name -> (cons : List ITy) -> Decl
simpleData v n = iData v n type []

enumDecl : (name : String) -> (cons : List String) -> Decl
enumDecl name = simpleData Public (UN $ Basic name) . map mkCon
  where mkCon : String -> ITy
        mkCon n = mkTy (UN $ Basic n) (varStr name)

export
mkEnum : (name : String) -> (cons : List String) -> Elab ()
mkEnum name cons = do
  logMsg "grr" 1 ("yesss")
  declare [enumDecl name cons]

%runElab mkEnum "Gender" ["Female","Male","NonBinary"]

foo : Nat
foo = 2

Show (Elab ()) where
  show x = ""
{--}
