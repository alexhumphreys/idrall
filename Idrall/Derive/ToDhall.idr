module Idrall.Derive.ToDhall

import Idrall.Expr
import Idrall.Pretty
import Idrall.Derive.Common

import public Data.SortedMap

import Language.Reflection

%language ElabReflection

%hide Idrall.Expr.Name

public export
interface ToDhall ty where
  constructor MkToDhall
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

parameters (options : Options)
  -- Record Type functions
  -- given a idris Record constructor arg in the form (Name, type),
  -- return a dhall record field for use in the ERecord constructor.
  argToFieldType : List (Name, TTImp) -> TTImp
  argToFieldType [] = `([])
  argToFieldType ((n, t) :: xs) =
    let name = primStr $ options.fieldNameModifier (show n)
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
    let name = primStr $ options.fieldNameModifier (show n)
    in `(MkPair (MkFieldName ~name) (toDhall (~(var n) ~(var arg))) :: ~(argToField arg xs))

  dhallRecLitFromRecArg : Name -> List (Name, TTImp) -> TTImp
  dhallRecLitFromRecArg arg xs =
    `(ERecordLit EmptyFC $ fromList $ ~(argToField arg xs))

  genRecordLitClauses : Name -> Name -> Cons -> List Clause
  genRecordLitClauses funName arg [] = do
    pure $ patClause `(~(var funName) ~(bindvar $ show arg)) (dhallRecLitFromRecArg arg [])
  genRecordLitClauses funName arg ((n, ls) :: xs) = do
    pure $ patClause `(~(var funName) ~(bindvar $ show arg)) (dhallRecLitFromRecArg arg ls)

  deriveToDhallRecord :  Name
                      -> Name
                      -> Name
                      -> Cons
                      -> Elab ()
  deriveToDhallRecord name funNameType funNameLit cons =
    let argName = genReadableSym "arg"
        funDeclType = IDef EmptyFC funNameType $ (genRecordTypeClauses funNameType !argName cons)
        funDeclLit = IDef EmptyFC funNameLit $ (genRecordLitClauses funNameLit !argName cons)
    in do
      -- declare the fuction in the env
      declare [funDeclType, funDeclLit]

-- ADT Type functions
mkUnion : Name -> Cons -> Elab (TTImp)
mkUnion n cons = pure `(EUnion EmptyFC $ fromList $ ~(!(go n cons)))
  where
  getTypeTTImp : Name -> List (Name, TTImp) -> Elab (TTImp)
  getTypeTTImp consName [] =
    let cn = primStr $ show $ stripNs consName in
    do
      pure `(MkPair (MkFieldName ~cn) Nothing)
  getTypeTTImp consName ((n, t) :: []) =
    let cn = primStr $ show $ stripNs consName in
    do
      pure $ `(MkPair (MkFieldName ~cn) $ Just (toDhallType {ty = ~t}))
  getTypeTTImp consName (_ :: xs) = do
     fail $ "too many args for constructor: " ++ show consName
  go : Name -> Cons -> Elab (TTImp)
  go name [] = pure `([])
  go name ((n, t) :: xs) = do
    pair <- getTypeTTImp n t
    pure $ `(~(pair) :: ~(!(go name xs)))

genClauseADT : Name -> Name -> Name -> List (Name, TTImp) -> Elab (TTImp, TTImp)
genClauseADT name funName constructor' xs =
  let cnShort = show $ stripNs $ constructor'
      cn = primStr cnShort
      nameShort = show $ stripNs $ name
      lhs0 = `(~(var funName) ~(var constructor'))
      toDhallTypeFunName = "toDhallType" ++ nameShort
      fieldName = IPrimVal EmptyFC $ Str cnShort
  in do
    case xs of
         [] => pure $ MkPair lhs0
            `(EField EmptyFC (~(varStr toDhallTypeFunName)) (MkFieldName ~cn))
         ((n, t) :: []) => do
            argName <- genReadableSym "arg"
            pure $ MkPair
              `(~(var funName) (~(varStr cnShort) ~(bindvar $ show argName)))
              `(EApp EmptyFC (EField EmptyFC (~(varStr toDhallTypeFunName)) (MkFieldName ~fieldName)) (toDhall ~(var argName)))
         (x :: _) => fail $ "too many args for constructor: " ++ show constructor'

deriveToDhallADT : Name
                 -> Name
                 -> Name
                 -> Cons
                 -> Elab ()
deriveToDhallADT name funNameType funNameLit cons = do
  -- given constructors, lookup names in dhall records for those constructors
  rhs <- mkUnion name cons
  clausesType <- pure $ patClause
     `(~(var funNameType)) rhs
  let funDeclType = IDef EmptyFC funNameType [clausesType]
  declare [funDeclType]

  clausesADTLit <- traverse (\(cn, as) => genClauseADT name funNameLit cn (reverse as)) cons
  clausesLit <- pure $ map (\x => patClause (fst x) (snd x)) clausesADTLit
  let funDeclLit = IDef EmptyFC funNameLit clausesLit
   -- declare []
  declare [funDeclLit]

toDhallImpl : String -> List Decl
toDhallImpl typeName =
  let -- names
      mkToDhall = UN $ Basic "MkToDhall"
      toDhallType = UN $ Basic "toDhallType"
      toDhallName = UN $ Basic "toDhall"
      rhsToDhallType = UN $ Basic $ "toDhallType" ++ typeName
      rhsToDhallLit = UN $ Basic $ "toDhallLit" ++ typeName
      functionName = UN . Basic $ "implToDhall" ++ typeName

      typeNameImp = var $ UN $ Basic typeName
      toDhallType = var toDhallType
      toDhall = var toDhallName
      function = var functionName

      toDhallLitClause = patClause toDhall $ var rhsToDhallLit

      impl = ILocal EmptyFC
          [ IClaim $ NoFC $ MkIClaimData MW Private [] (MkTy EmptyFC (NoFC toDhallName) `(~(typeNameImp) -> Expr Void))
          , IDef EmptyFC toDhallName [toDhallLitClause]
          ]
          `(~(var mkToDhall) ~(var rhsToDhallType) ~(var rhsToDhallLit))

  in [ IClaim $ NoFC $ MkIClaimData MW Public [Hint True] $ MkTy EmptyFC (NoFC functionName) `(ToDhall ~(typeNameImp))
     , IDef EmptyFC functionName [patClause function impl]
     ]

export
deriveToDhall : IdrisType
              -> {default Common.defaultOptions options : Options}
              -> (name : Name)
              -> Elab ()
deriveToDhall it {options} n = do
  [(name, _)] <- getType n
          | _ => fail "Ambiguous name"
  let nameShortStr = show (stripNs name)
  let funNameType = UN $ Basic ("toDhallType" ++ nameShortStr)
  let funNameLit = UN $ Basic ("toDhallLit" ++ nameShortStr)
  let objNameType = UN $ Basic ("__impl_toDhallType" ++ nameShortStr)
  let objNameLit = UN $ Basic ("__impl_toDhallLit" ++ nameShortStr)

  conNames <- getCons name

  -- get the constructors of the record
  -- cons : (List (Name, List (Name, TTImp)))
  cons <- for conNames $ \n => do
    [(conName, conImpl)] <- getType n
      | _ => fail $ show n ++ "constructor must be in scope and unique"
    args <- getArgs conImpl
    pure (conName, args)

  -- logCons cons

  -- create the function type signatures
  let funClaimType = IClaim $ NoFC $ MkIClaimData MW Export [Inline] (MkTy EmptyFC (NoFC funNameType) `(Expr Void))
  let funClaimLit = IClaim $ NoFC $ MkIClaimData MW Export [Inline] (MkTy EmptyFC (NoFC funNameLit) `(~(var name) -> Expr Void))

  -- declare the function type signatures in the env
  declare [funClaimType, funClaimLit]
  case it of
       Record => do
         deriveToDhallRecord options name funNameType funNameLit cons
         declare $ toDhallImpl $ nameShortStr
       ADT => do
         deriveToDhallADT name funNameType funNameLit cons
         declare $ toDhallImpl $ nameShortStr

-- Record example
record ExRec1 where
  constructor MkExRec1
  mn : Maybe Nat
  st : String

%runElab (deriveToDhall Record `{ ExRec1 })

data ExADTTest
  = Bar
  | ADouble Double
%runElab (deriveToDhall ADT `{ ExADTTest })

data Ex1
  = ANat Nat
  | ADoub Double
  | ANone

