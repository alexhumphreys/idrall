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

-- ADT Type functions
argToADTFieldType : List (Name, TTImp) -> TTImp
argToADTFieldType [] = `([])
argToADTFieldType ((n, t) :: xs) =
  let name = primStr $ (show n)
  in `(MkPair (MkFieldName ~name) (toDhallType {ty = ~t}) :: ~(argToFieldType xs))

foo : Name -> Maybe (Name, TTImp) -> (FieldName, Maybe (Expr Void))
foo constructor' xs =
  let cn = (show $ stripNs constructor')
  in
    case xs of
         Nothing => do
           MkPair (MkFieldName cn) (the (Maybe (Expr Void)) Nothing)
         Just (n, t) => do
           MkPair (MkFieldName cn) (the (Maybe (Expr Void)) Nothing)

genFromList : List (Name, List (Name, TTImp)) -> Elab (List (FieldName, Maybe (Expr Void)))
genFromList [] = pure $ []
-- genFromList ((cn, args) :: xs) = pure $ `(!(foo cn args) :: !(genFromList xs))
genFromList ((cn, args) :: xs) =
  case args of
       [] =>
         let x = foo cn Nothing in
         do pure $ [x]
       (x :: []) => pure $ []
       x => pure $ []

genClauseADTType : Name -> Name -> Name -> List (Name, TTImp) -> Elab (FieldName, Maybe (Expr Void))
genClauseADTType name funName constructor' xs =
  let cn = (show $ stripNs constructor')
      debug = show $ constructor'
      debug2 = show $ map fst xs
      lhs0 = `(~(var funName))
  in do
  logMsg "here" 0 debug
  logMsg "here" 0 debug2
  case xs of
       [] => pure $ MkPair (MkFieldName cn) (Nothing)
       ((n, t) :: []) => do
         pure $ MkPair (MkFieldName cn) (Nothing)
       (x :: _) => fail $ "too many args for constructor: " ++ show constructor'

genClauseADT : Name -> Name -> List (Name, TTImp) -> Elab (TTImp, TTImp)
genClauseADT funName constructor' xs =
  let cn = primStr (show $ stripNs constructor')
      debug = show $ constructor'
      debug2 = show $ map fst xs
      lhs0 = `(~(var funName) ~(var constructor'))
  in do
    case xs of
         [] => pure $ MkPair lhs0
            -- TODO fix EText EmptyFC here
            `(EField EmptyFC (EText EmptyFC) (MkFieldName ~cn))
         ((n, t) :: []) => do
            argName <- genReadableSym "arg"
            pure $ MkPair
              `(~(var funName) (~(var constructor') argName))
              `(EApp EmptyFC (EField EmptyFC (toDhallType) (MkFieldName ~(var constructor'))) (toDhall x))
         (x :: _) => fail $ "too many args for constructor: " ++ show constructor'

deriveToDhallADT : Name
                 -> Name
                 -> Name
                 -> Cons
                 -> Elab ()
deriveToDhallADT name funNameType funNameLit cons = do
  -- given constructors, lookup names in dhall records for those constructors
  stuff <- genFromList cons
  let rhs = `(EUnion EmptyFC $ fromList stuff)
  clausesType <- pure $ patClause
     `(~(var funNameType)) rhs
  let funDeclType = IDef EmptyFC funNameType [clausesType]
  declare [funDeclType]

  clausesADTLit <- traverse (\(cn, as) => genClauseADT funNameLit cn (reverse as)) cons
  clausesLit <- pure $ map (\x => patClause (fst x) (snd x)) clausesADTLit
  let funDeclLit = IDef EmptyFC funNameLit clausesLit
   -- declare []
  declare [funDeclLit]

export
deriveToDhall : IdrisType
              -> (name : Name)
              -> Elab ()
deriveToDhall it n = do
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

  case it of
       Record => deriveToDhallRecord name funNameType funNameLit cons
       ADT => deriveToDhallADT name funNameType funNameLit cons

-- Record example
record ExRec1 where
  constructor MkExRec1
  mn : Maybe Nat
  st : String

%runElab (deriveToDhall Record `{ ExRec1 })

data ExADTTest
  = Bar
  | ADouble Double
-- %runElab (deriveToDhall ADT `{ ExADTTest })

data Ex1
  = ANat Nat
  | ADoub Double
  | ANone

forDebug : List (String, Maybe Type)

forDebug2 : (name : Name)
          -> Elab ()
forDebug2 n = do
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

  logMsg "yyyy" 0 $ show name
  logCons cons
  let lhs = `(~(var (UN $ Basic "forDebug")))
  rhs <- go name cons
  let foo = IDef EmptyFC (UN $ Basic "forDebug") $ [patClause lhs rhs]
  declare [foo]
  where
      --logTerm "" 0 "this guy" t
    getTypeTTImp : Name -> List (Name, TTImp) -> Elab (TTImp)
    getTypeTTImp consName [] =
      let cn = primStr $ show $ stripNs consName in
      do
        pure `(MkPair ~cn Nothing)
    getTypeTTImp consName ((n, t) :: []) =
      let cn = primStr $ show $ stripNs consName in
      do
        pure $ `(MkPair ~cn $ Just ~t)
    getTypeTTImp consName (_ :: xs) = do
      pure `(MkPair $ "" Nothing)

    someLogging : List (Name, TTImp) -> Elab ()
    someLogging [] = pure ()
    someLogging ((n, t) :: xs) = do
      logTerm "" 0 "this guy" t
      someLogging xs
    go : Name -> Cons -> Elab (TTImp)
    go name [] = pure `([])
    go name ((n, t) :: xs) = do
      logMsg " " 0 $ show n
      someLogging t
      x <- getTypeTTImp n t
      pure $ `(~(x) :: ~(!(go name xs)))
      -- pure $ `(~(!(getTypeTTImp t)) :: ~(!(go name xs)))
      -- pure $ `((MkPair (show n) ~(var name)) :: !(go name xs))

%runElab (forDebug2 `{ Ex1 })
{--}
