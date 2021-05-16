module Idrall.Derive

import Language.Reflection
import Data.List1
import public Data.String

import Idrall.Expr

%language ElabReflection

%hide Idrall.Expr.Name
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
||| Names are best created using quotes: `{{ AName }},
||| `{{ In.Namespacs.Name }}.
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
          run (h ::: []) []        = UN h
          run (h ::: []) ns        = NS (MkNS ns) (UN h)
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
stripNs : Name -> Name
stripNs (NS _ x) = x
stripNs x = x

||| from idris2-lsp
covering
genReadableSym : String -> Elab Name
genReadableSym hint = do
  MN v i <- genSym hint
    | _ => fail "cannot generate readable argument name"
  pure $ UN (v ++ show i)

||| from idris2-lsp
primStr : String -> TTImp
primStr = IPrimVal EmptyFC . Str

||| from idris2-lsp
bindvar : String -> TTImp
bindvar = IBindVar EmptyFC

||| from idris2-lsp
implicit' : TTImp
implicit' = Implicit EmptyFC True

||| moved from where clause
getArgs : TTImp -> Elab (List (Name, TTImp))
getArgs (IPi _ _ _ (Just n) argTy retTy) = ((n, argTy) ::) <$> getArgs retTy
getArgs (IPi _ _ _ Nothing _ _) = fail $ "All arguments must be explicitly named"
getArgs _ = pure []

logCons : (List (Name, List (Name, TTImp))) -> Elab ()
logCons [] = pure ()
logCons (x :: xs) = do
  more x
  logCons xs
where
  go : List (Name, TTImp) -> Elab ()
  go [] =  pure ()
  go ((n, t) :: ys) = do
    logMsg "" 0 ("Name: " ++ show n)
    logTerm "" 0 "Type" t
    go ys
  more : (Name, List (Name, TTImp)) -> Elab ()
  more (n, xs) = do
    logMsg "" 0 ("name1: " ++ show n)
    go xs

public export
interface FromDhall a where
  fromDhall : Expr Void -> Maybe a

export
FromDhall Nat where
  fromDhall (ENaturalLit x) = pure x
  fromDhall _ = neutral

export
FromDhall Bool where
  fromDhall (EBoolLit x) = pure x
  fromDhall _ = neutral

export
FromDhall Integer where
  fromDhall (EIntegerLit x) = pure x
  fromDhall _ = neutral

export
FromDhall Double where
  fromDhall (EDoubleLit x) = pure x
  fromDhall _ = neutral

export
FromDhall a => FromDhall (List a) where
  fromDhall (EListLit _ xs) = pure $ !(traverse fromDhall xs)
  fromDhall _ = neutral

export
FromDhall a => FromDhall (Maybe a) where
  fromDhall (ESome x) = pure $ fromDhall x
  fromDhall ENone = neutral
  fromDhall _ = neutral

export
deriveFromDhall : (name : Name) -> Elab ()
deriveFromDhall n =
  do [(n, _)] <- getType n
             | _ => fail "Ambiguous name"
     -- logMsg "" 0 ("Resolved name: " ++ show n)

     let funName = UN ("fromDhall" ++ show (stripNs n))
     -- logMsg "" 0 ("funName: " ++ show funName)

     let objName = UN ("__impl_fromDhall" ++ show (stripNs n))
     -- logMsg "" 0 ("objName: " ++ show objName)

     conNames <- getCons n
     -- logMsg "" 0 ("Constructors: " ++ show conNames)

     argName <- genReadableSym "arg"
     -- logMsg "" 0 ("argName: " ++ show argName)

     -- get the constructors of the record
     cons <- for conNames $ \n => do
       [(conName, conImpl)] <- getType n
         | _ => fail $ show n ++ "constructor must be in scope and unique"
       args <- getArgs conImpl
       pure (conName, args)

     logCons cons

     -- given constructors, lookup names in json object for those constructors
     clauses <- traverse (\(cn, as) => genClause funName cn argName (reverse as)) cons

     -- create function from JSON to Maybe Example
     -- using the above clauses as patterns
     let name = n
     let clauses = [patClause `(~(var funName) (ERecordLit ~(bindvar $ show argName)))
                              (foldl (\acc, x => `(~x <|> ~acc)) `(Nothing) (clauses))]
     let funClaim = IClaim EmptyFC MW Export [Inline] (MkTy EmptyFC EmptyFC funName `(Expr Void -> Maybe ~(var name)))
     -- add a catch all pattern
     let funDecl = IDef EmptyFC funName (clauses ++ [patClause `(~(var funName) ~implicit') `(Nothing)])

     -- declare the fuction in the env
     declare [funClaim, funDecl]
     [(ifName, _)] <- getType `{{FromDhall}}
       | _ => fail "FromDhall interface must be in scope and unique"
     [NS _ (DN _ ifCon)] <- getCons ifName
       | _ => fail "Interface constructor error"

     -- created interface for Example, and use function we already declared
     let retty = `(FromDhall ~(var name))
     let objClaim = IClaim EmptyFC MW Export [Hint True, Inline] (MkTy EmptyFC EmptyFC objName retty)
     let objrhs = `(~(var ifCon) ~(var funName))
     let objDecl = IDef EmptyFC objName [(PatClause EmptyFC (var objName) objrhs)]
     declare [objClaim, objDecl]
  where
    ||| moved from where clause
    genClause : Name -> Name -> Name -> List (Name, TTImp) -> Elab (TTImp)
    genClause funName t m xs = do
          let rhs = foldr (\(n, type), acc =>
                            let name = primStr $ (show n) in
                                case type of
                                     `(Prelude.Types.Maybe _) => do
                                       `(~acc <*> (pure $ lookup (MkFieldName ~name) ~(var m) >>= fromDhall))
                                     _ => `(~acc <*> (lookup (MkFieldName ~name) ~(var m) >>= fromDhall)))
                          `(pure ~(var t)) xs
          logMsg "" 0 ("hellloo")
          pure (rhs)
