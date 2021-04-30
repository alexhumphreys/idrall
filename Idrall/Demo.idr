import Idrall.APIv1
import Idrall.Value
import Idrall.Expr
import Idrall.Eval
import Idrall.Error
import Idrall.IOEither
import Data.SortedMap

record Package where
  constructor MkPackage
  package : String
  sourcedir : Maybe String
  depends : Maybe $ List String
  modules : List String

lookupField : SortedMap FieldName Value -> String -> Either Error Value
lookupField sm k =
  case lookup (MkFieldName k) sm of
       Nothing => Left $ ErrorMessage $ "missing needed key: " ++ k
       (Just v) =>  Right v

dhallStringToIdrisString : Value -> Either Error String
dhallStringToIdrisString v@(VTextLit (MkVChunks xs x)) =
  case strFromChunks xs of
       Nothing => Left $ ErrorMessage $ "is not a String: " ++ show v
       (Just y) => Right $ y ++ x
dhallStringToIdrisString x = Left $ ErrorMessage $ "is not a String: " ++ show x

maybeValToMaybeString : Maybe Value -> Either Error $ Maybe String
maybeValToMaybeString Nothing = Right Nothing
maybeValToMaybeString (Just x) = Right $ Just $ !(dhallStringToIdrisString x)

dhallListToIdrisList : Value -> Either Error $ List Value
dhallListToIdrisList (VListLit _ xs) = Right xs
dhallListToIdrisList x = Left $ ErrorMessage $ "Not a List: " ++ show x

listValToListString : List Value -> Either Error $ List String
listValToListString [] = Right []
listValToListString (x :: xs) =
  let rest = listValToListString xs
      x' = dhallStringToIdrisString x
  in [| x' :: rest |]

maybeValToMaybeListString : Maybe Value -> Either Error $ Maybe (List String)
maybeValToMaybeListString Nothing = Right Nothing
maybeValToMaybeListString (Just x) =
  let ls = dhallListToIdrisList x in
  Right $ Just $ !(listValToListString !ls)

dhallOptionalToIdrisMaybe : Value -> Either Error $ Maybe Value
dhallOptionalToIdrisMaybe (VNone x) = Right Nothing
dhallOptionalToIdrisMaybe (VSome x) = Right $ Just x
dhallOptionalToIdrisMaybe x = Left $ ErrorMessage $ "Not an Optional value: " ++ show x

dhallToPackage : Value -> Either Error Package
dhallToPackage (VRecordLit x) = do
  packageVal <- lookupField x "package"
  sourcedirVal <- lookupField x "sourcedir"
  dependsVal <- lookupField x "depends"
  modulesVal <- lookupField x "modules"
  packageStr <- dhallStringToIdrisString packageVal
  sourcedirMaybeString <- maybeValToMaybeString $ !(dhallOptionalToIdrisMaybe sourcedirVal)
  dependsMaybeListString <- maybeValToMaybeListString $ !(dhallOptionalToIdrisMaybe dependsVal)
  modulesListString <- listValToListString $ !(dhallListToIdrisList modulesVal)
  Right $ MkPackage packageStr sourcedirMaybeString dependsMaybeListString modulesListString
dhallToPackage x = Left $ ErrorMessage $ "not a record: " ++ show x

readPackageFile : IOEither Error Package
readPackageFile = do
  val <- roundTripCheckEval "./samples/package.dhall"
  liftEither $ dhallToPackage val

Show Package where
  show (MkPackage package sourcedir depends modules) =
    """
    package name is: \{package}
    root source dir is: \{show sourcedir}
    it depends on: \{show depends}
    its modules are: \{show modules}
    """

printPackage : IOEither Error Package -> IO String
printPackage (MkIOEither x) = do
  x' <- x
  case x' of
       (Left err) => pure $ show err
       (Right pkg) => pure $ show pkg

main : IO ()
main = do
  packageDescription <- printPackage readPackageFile
  putStrLn $ packageDescription
