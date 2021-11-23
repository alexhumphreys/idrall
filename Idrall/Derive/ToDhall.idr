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

deriveToDhallRecord : Name
                    -> Name
                    -> Name
                    -> Cons
                    -> Elab ()
deriveToDhallRecord name funNameType funNameLit cons =
  -- clauses <- genClauses funName argName cons
  let argName = genReadableSym "arg"
      funDeclType = IDef EmptyFC funNameType $ (genRecordTypeClauses funNameType !argName cons)
      funDeclLit = IDef EmptyFC funNameLit $ (genRecordLitClauses funNameLit !argName cons)
  in do
    -- declare the fuction in the env
    declare [funDeclType]
    declare [funDeclLit]

deriveToDhallADT : Name
                 -> Name
                 -> Cons
                 -> Elab ()
deriveToDhallADT funName arg cons = ?foo2

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

  -- create the function type signatures
  let funClaimType = IClaim EmptyFC MW Export [Inline] (MkTy EmptyFC EmptyFC funNameType `(Expr Void))
  let funClaimLit = IClaim EmptyFC MW Export [Inline] (MkTy EmptyFC EmptyFC funNameLit `(~(var name) -> Expr Void))
  -- declare the function type signatures in the env
  declare [funClaimType, funClaimLit]

  -- declare the function bodies in the env
  deriveToDhallRecord name funNameType funNameLit cons

-- Record example
record ExRec1 where
  constructor MkExRec1
  mn : Maybe Nat
  st : String

%runElab (deriveToDhall `{ ExRec1 })

{--}
