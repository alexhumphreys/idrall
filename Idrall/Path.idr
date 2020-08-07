module Idrall.Path

public export
Dir : Type
Dir = List String

public export
data Path
  = Home Dir
  | Absolute Dir
  | Relative Dir

public export
Show Path where
  show (Home xs) = "(Home " ++ show xs ++ ")"
  show (Absolute xs) = "(Absolute " ++ show xs ++ ")"
  show (Relative xs) = "(Relative " ++ show xs ++ ")"

public export
record FilePath where
  constructor MkFilePath
  path : Path
  fileName : Maybe String

public export
Show FilePath where
  show x = "(MkFilePath " ++ (show (path x)) ++ " " ++ (show (fileName x)) ++ ")"

-- TODO replace with new Normal type that takes PWD and $HOME
public export
Eq FilePath where
  (==) (MkFilePath (Home xs) fileName) (MkFilePath (Home ys) x) = (xs == ys) && (fileName == x)
  (==) (MkFilePath (Absolute xs) fileName) (MkFilePath (Absolute ys) x) = (xs == ys) && (fileName == x)
  (==) (MkFilePath (Relative xs) fileName) (MkFilePath (Relative ys) x) = (xs == ys) && (fileName == x)
  (==) _ _ = False

public export
normalisePath : Dir -> Dir
normalisePath [] = []
normalisePath ("." :: xs) = normalisePath xs
normalisePath (".." :: xs) = normalisePath xs
normalisePath (x :: ".." :: xs) = normalisePath xs
normalisePath (x :: xs) = x :: normalisePath xs

public export
normaliseFilePath : FilePath -> FilePath
normaliseFilePath (MkFilePath (Home xs) fileName) = MkFilePath (Home (normalisePath xs)) fileName
normaliseFilePath (MkFilePath (Absolute xs) fileName) = MkFilePath (Absolute (normalisePath xs)) fileName
normaliseFilePath (MkFilePath (Relative xs) fileName) = MkFilePath (Relative (normalisePath xs)) fileName

public export
pathFromDir : Dir -> Path
pathFromDir [] = Absolute [] -- TODO maybe rethink this
pathFromDir d@("." :: xs) = Relative d
pathFromDir d@(".." :: xs) = Relative d
pathFromDir d@("~" :: xs) = Home d
pathFromDir d = Absolute d

public export
addSlashes : Dir -> String
addSlashes x = concat (intersperse "/" x)

public export
prettyPrintPath : Path -> String
prettyPrintPath (Home xs) = "~/" ++ (addSlashes xs)
prettyPrintPath (Absolute xs) = "/" ++ (addSlashes xs)
prettyPrintPath (Relative xs) = (addSlashes xs)

public export
splitOnFile : Dir -> (Dir, Maybe String)
splitOnFile [] = ([], Nothing)
splitOnFile [x] = ([], Just x)
splitOnFile (x :: xs) =
  let (dir, file) = splitOnFile xs in
      (x :: dir, file)

public export
mkFilePath : (Dir, Maybe String) -> (Dir -> Path) -> FilePath
mkFilePath (a, b) f = MkFilePath (f a) b

public export
filePathFromPath : Path -> FilePath -- TODO dry
filePathFromPath (Home xs) = mkFilePath (splitOnFile xs) (Home)
filePathFromPath (Absolute xs) = mkFilePath (splitOnFile xs) (Absolute)
filePathFromPath (Relative xs) = mkFilePath (splitOnFile xs) (Relative)

public export
filePathForIO : FilePath -> String -- TODO Check how this handles empty paths
filePathForIO (MkFilePath path Nothing) = prettyPrintPath path
filePathForIO (MkFilePath path (Just x)) = (prettyPrintPath path) ++ "/" ++ x
