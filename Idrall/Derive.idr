module Idrall.Derive

import Language.Reflection
import Data.List1
import public Data.String

import Idrall.Expr
import Idrall.Error
import Idrall.Eval

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
stripNs : Name -> Name
stripNs (NS _ x) = x
stripNs x = x

||| from idris2-lsp
covering
genReadableSym : String -> Elab Name
genReadableSym hint = do
  MN v i <- genSym hint
    | _ => fail "cannot generate readable argument name"
  pure $ UN $ Basic (v ++ show i)

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

Cons : Type
Cons = (List (Name, List (Name, TTImp)))

logCons : Cons -> Elab ()
logCons [] = pure ()
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

public export
interface FromDhall a where
  fromDhall : Expr Void -> Either Error a

fromDhallErr : Expr Void -> String -> Either Error a
fromDhallErr e str = Left $ FromDhallError (getFC e) str

export
FromDhall Nat where
  fromDhall (ENaturalLit fc x) = pure x
  fromDhall e = fromDhallErr e "not a Nat"

export
FromDhall Bool where
  fromDhall (EBoolLit fc x) = pure x
  fromDhall e = fromDhallErr e "not a Bool"

export
FromDhall Integer where
  fromDhall (EIntegerLit fc x) = pure x
  fromDhall e = fromDhallErr e "not an Int"

export
FromDhall Double where
  fromDhall (EDoubleLit fc x) = pure x
  fromDhall e = fromDhallErr e "not a Double"

export
FromDhall String where
  fromDhall e =
    let str = strFromExpr e in
    case str of
         Nothing => fromDhallErr e "couldn't normalise string"
         (Just y) => pure y

export
FromDhall a => FromDhall (List a) where
  fromDhall (EListLit fc _ xs) = pure $ !(traverse fromDhall xs)
  fromDhall e = fromDhallErr e "not a List"

export
FromDhall a => FromDhall (Maybe a) where
  fromDhall (ESome fc x) =
    pure $ Just !(fromDhall x)
  fromDhall (EApp fc (ENone fc') _) = pure $ neutral
  fromDhall e = fromDhallErr e "not a Maybe"

||| Used with FromDhall interface, to dervice implementations
||| for ADTs or Records
public export
data IdrisType
  = ADT
  | Record

public export
lookupEither : Show k => k -> SortedMap k v -> Either Error v
lookupEither k sm =
  case lookup k sm of
       Nothing => Left $ FromDhallError initFC $ "key \{show k} not found"
       (Just x) => pure x

Alternative (Either Error) where
  empty = Left $ FromDhallError initFC "Alternative failed"
  (Left x) <|> y = y
  (Right x) <|> _ = (Right x)

export
deriveFromDhall : IdrisType -> (name : Name) -> Elab ()
deriveFromDhall it n =
  do [(name, _)] <- getType n
             | _ => fail "Ambiguous name"
     let funName = UN $ Basic ("fromDhall" ++ show (stripNs name))
     let objName = UN $ Basic ("__impl_fromDhall" ++ show (stripNs name))

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

     clauses <- genClauses it funName argName cons

     let funClaim = IClaim EmptyFC MW Export [Inline] (MkTy EmptyFC EmptyFC funName `(Expr Void -> Either Error ~(var name)))
     -- add a catch all pattern
     let funDecl = IDef EmptyFC funName (clauses ++ [patClause `(~(var funName) ~(varStr "expr")) `(Left $ FromDhallError (getFC ~(varStr "expr")) "\{show expr}")])

     -- declare the fuction in the env
     declare [funClaim, funDecl]
     [(ifName, _)] <- getType `{FromDhall}
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
    ||| moved from where clause, used for record constuctors
    genClauseRecord : Name -> Name -> List (Name, TTImp) -> Elab (TTImp)
    genClauseRecord constructor' arg xs = do
          let rhs = foldr (\(n, type), acc =>
                            let name = primStr $ (show n) in
                                case type of
                                     _ => `(~acc <*> (lookupEither (MkFieldName ~name) ~(var arg) >>= fromDhall)))
                          `(pure ~(var constructor')) xs
          pure (rhs)
    genClauseADT : Name -> Name -> Name -> List (Name, TTImp) -> Elab (TTImp, TTImp)
    genClauseADT funName constructor' arg xs =
      let cn = primStr (show $ stripNs constructor')
          debug = show $ constructor'
          debug2 = show $ map fst xs
          lhs0 = `(~(var funName) (EField _ (EUnion _ xs) (MkFieldName ~cn)))
          lhs1 = `(~(var funName) (EApp fc (EField _ (EUnion _ xs) (MkFieldName ~cn)) ~(bindvar $ show arg)))
          -- TODO lhsN for data constructors with more than 0 or 1 args
          in do
          case xs of
               [] => pure $ (lhs0, `(pure ~(var constructor')))
               ((n, _) :: []) => pure $ (lhs1, `(pure ~(var constructor') <*> fromDhall ~(var arg)))
               (x :: _) => fail $ "too many args for constructor: " ++ show constructor'
    genClauses : IdrisType -> Name -> Name -> Cons -> Elab (List Clause)
    genClauses ADT funName arg cons = do
      -- given constructors, lookup fields in dhall unions for those constructors
      clausesADT <- traverse (\(cn, as) => genClauseADT funName cn arg (reverse as)) cons
      pure $ map (\x => patClause (fst x) (snd x)) clausesADT
    genClauses Record funName arg cons = do
      -- given constructors, lookup names in dhall records for those constructors
      clausesRecord <- traverse (\(cn, as) => genClauseRecord cn arg (reverse as)) cons
      -- create clause from dhall to `Maybe a` using the above clauses as the rhs
      pure $ pure $ patClause `(~(var funName) (ERecordLit fc ~(bindvar $ show arg)))
                              (foldl (\acc, x => `(~x)) `(Left $ FromDhallError ~(varStr "fc") "failed1") (clausesRecord)) -- not a real foldl, basically just passes that clausesRecord though, also doesn't support a record with no args

record ExRec1 where
  constructor MkExRec1
  n : Nat
  i : Integer

data Foo = I | J Nat

%runElab (deriveFromDhall Record `{ ExRec1 })

%runElab (deriveFromDhall ADT `{ Foo })

bam1 : Expr Void -> Either Error ExRec1
bam1 (ERecordLit fc arg12128) = ((pure MkExRec1 <*> (lookupEither (MkFieldName "n") arg12128 >>= fromDhall)) <*> (lookupEither (MkFieldName "i") arg12128 >>= fromDhall)) -- <|> Delay (Left (FromDhallError fc "failed1"))
bam1 expr = Left (FromDhallError (getFC expr) "failed2")

ex1 : Expr Void
ex1 = ERecordLit initFC $ fromList
  [ (MkFieldName "n", ENaturalLit initFC 0)
  , (MkFieldName "i", ENaturalLit (MkFC Nothing (0,0) (0,1)) 0)
  ]

{-
ex2 : Expr Void
ex2 = EField EUnion initFC $ fromList
  [ (MkFieldName "I", Nothing)
  -- , (MkFieldName "i", ENaturalLit (MkFC Nothing (0,0) (0,1)) 0)
  ]
  -}
