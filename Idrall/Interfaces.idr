module Idrall.Interfaces

import public Data.Maybe
import Data.SortedMap
import Idrall.Expr
import Language.Reflection
import Idrall.Syntax
import public Idrall.Types
import Debug.Trace
import Idrall.Pretty

%language ElabReflection

||| A type that can be possibly converted from Dhall.
||| An example type and implementation is:
||| ```idris example
||| record Position where
|||   constructor MkPosition
|||   x : Integer
|||   y : Integer
|||
||| FromDhall Position where
|||   fromDhall (JObject arg) = do
|||     x <- lookup "x" arg >>= fromJSON
|||     y <- lookup "y" arg >>= fromJSON
|||     pure $ MkPosition x y
|||   fromDhall _ = neutral
||| ```
public export
interface FromDhall a where
  fromDhall : Expr Void -> Maybe a

export
FromDhall Integer where
  fromDhall (EIntegerLit x) = pure x
  fromDhall _ = neutral

export
FromDhall Int where
  fromDhall (EIntegerLit x) = pure $ cast x
  fromDhall _ = neutral

export
FromDhall Double where
  fromDhall (EDoubleLit x) = pure $ cast x
  fromDhall _ = neutral

export
FromDhall Nat where
  fromDhall (ENaturalLit x) = pure x
  fromDhall _ = neutral

export
FromDhall Bool where
  fromDhall (EBoolLit x) = pure x
  fromDhall _ = neutral

export
FromDhall a => FromDhall (Maybe a) where
  fromDhall ENone = pure Nothing
  fromDhall (ESome x) = pure <$> fromDhall x
  fromDhall _ = neutral

export
FromDhall a => FromDhall (List a) where
  fromDhall (EListLit _ x) = traverse fromDhall x
  fromDhall _ = neutral

export
FromDhall b => FromDhall (SortedMap String b) where
  fromDhall (ERecordLit xs) =
    let vals = traverse {b} fromDhall xs in
        mapKeys <$> vals
    where
      go : List (FieldName, a) -> List (String, a)
      go [] = []
      go ((MkFieldName k,v) :: xs) = (k,v) :: go xs
      mapKeys : SortedMap FieldName a -> SortedMap String a
      mapKeys x = fromList $ go (toList x)

  fromDhall _ = neutral

public export
record JSONDeriveOpts where
  constructor MkOpts
  ||| If tagged, values are converted to JSON object with one field where the
  ||| key is the name of the constructor and the value is the object obtained
  ||| from converting the arguments of the constructor.
  tagged : Bool
  ||| Renaming rules for arguments where the name of the argument does not
  ||| match the correspondent key in the translated JSON object.
  renames : List (String, String)
  ||| Fields that must be present in the JSON translation but have static
  ||| values.
  staticFields : List (String, Expr Void)

%hide Idrall.Expr.Name

%hide Idrall.Syntax.var
var : Name -> TTImp
var = IVar EmptyFC

primStr : String -> TTImp
primStr = IPrimVal EmptyFC . Str

stripNs : Name -> Name
stripNs (NS _ x) = x
stripNs x = x

bindvar : String -> TTImp
bindvar = IBindVar EmptyFC

patClause : TTImp -> TTImp -> Clause
patClause = PatClause EmptyFC

implicit' : TTImp
implicit' = Implicit EmptyFC True

covering
genReadableSym : String -> Elab Name
genReadableSym hint = do
  MN v i <- genSym hint
    | _ => fail "cannot generate readable argument name"
  pure $ UN (v ++ show i)

public export
defaultOpts : JSONDeriveOpts
defaultOpts = MkOpts False [] []

export
record Example where
  constructor MkExample
  foo : Maybe Bool

eqDecl1 : String -> List String -> List Decl
eqDecl1 enumName cons =
  let functionName = UN $ "impl1Eq" ++ enumName
      function     = var functionName
      enum         = arg $ varStr enumName

      -- Default clause for non-matching constructors:
      -- `function _ _ = False`
      defClause    = function .$ implicitTrue .$ implicitTrue .= `(False)

      -- Pattern clause for a single constructor:
      -- `function A A = True`
      conClause    = \c => function .$ varStr c .$ varStr c .= `(True)

   in [ public' functionName $ enum .-> enum .-> `(Bool)
      , def functionName $ map conClause cons ++ [defClause] ]

mkEq1 : String -> List String -> Elab ()
mkEq1 n cons = declare $ eqDecl1 n cons

deriveFromDhall : (opts : JSONDeriveOpts) -> (name : Language.Reflection.TT.Name) -> Elab ()
deriveFromDhall opts n = do
    [(name, imp)] <- getType n
      | xs => trace (show n) $ fail $ show "balh"
    -- FIXME: temporary name for debugging, should be converted to a name impossible to define from users
    -- and should not be exported, unless a specific option is enabled.
    trace (show name) $ declare $ eqDecl1 "Gender" ["Female","Male","NonBinary"]
    {-
    let funName = UN ("fromDhall" ++ show (stripNs n))
    let objName = UN ("__impl_fromDhall" ++ show (stripNs n))
    conNames <- getCons name
    argName <- genReadableSym "arg"
    cons <- for conNames $ \n => do
      [(conName, conImpl)] <- getType n
        | _ => fail $ show n ++ "constructor must be in scope and unique"
      args <- getArgs conImpl
      pure (conName, args)
    ?koo
    clauses <- traverse (\(cn, as) => genClause funName cn argName (reverse as)) cons
    let clauses = if opts.tagged
                     then (uncurry patClause <$> clauses)
                     else [patClause `(~(var funName) (JObject ~(bindvar $ show argName)))
                                     (foldl (\acc, x => `(~x <|> ~acc)) `(Nothing) (snd <$> clauses))]
    let funClaim = IClaim EmptyFC MW Export [Inline] (MkTy EmptyFC EmptyFC funName `(Expr Void -> Maybe ~(var name)))
    let funDecl = IDef EmptyFC funName (clauses ++ [patClause `(~(var funName) ~implicit') `(Nothing)])
    declare [funClaim, funDecl]
    [(ifName, _)] <- getType `{FromDhall}
      | _ => fail "FromDhall interface must be in scope and unique"
    [NS _ (DN _ ifCon)] <- getCons ifName
      | _ => fail "Interface constructor error"
    let retty = `(FromDhall ~(var name))
    let objClaim = IClaim EmptyFC MW Export [Hint True, Inline] (MkTy EmptyFC EmptyFC objName retty)
    let objrhs = `(~(var ifCon) ~(var funName))
    let objDecl = IDef EmptyFC objName [(PatClause EmptyFC (var objName) objrhs)]
    declare [objClaim, objDecl]
    -}
  where
    getArgs : TTImp -> Elab (List (Name, TTImp))
    getArgs (IPi _ _ _ (Just n) argTy retTy) = ((n, argTy) ::) <$> getArgs retTy
    getArgs (IPi _ _ _ Nothing _ _) = fail $ "All arguments must be explicitly named"
    getArgs _ = pure []

    genClause : Name -> Name -> Name -> List (Name, TTImp) -> Elab (TTImp, TTImp)
    genClause funName t m xs = do
      let lhs = `(~(var funName) (JObject [MkPair ~(primStr $ show $ stripNs t) (JObject ~(bindvar $ show m))]))
      let rhs = foldr (\(n, type), acc => let name = primStr $ fromMaybe (show n) $ lookup (show n) opts.renames in
                                              case type of
                                                   `(Prelude.Types.Maybe _) => `(~acc <*> (pure $ lookup ~name ~(var m) >>= fromDhall))
                                                   _ => `(~acc <*> (lookup ~name ~(var m) >>= fromDhall)))
                      `(pure ~(var t)) xs
      r <- traverse (\(k, v) => (k,) <$> quote v) opts.staticFields
      let rhs = foldr (\(k, v), acc => `((lookup ~(primStr k) ~(var m) >>= (guard . (== ~v))) *> ~acc)) rhs r
      pure (lhs, rhs)

Show (Elab ()) where
  show x = "grrr"

export
exInfo : TypeInfo
exInfo = getInfo "Example"

