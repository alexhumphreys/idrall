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
normalisePath : Dir -> Dir
normalisePath [] = []
normalisePath ("." :: xs) = normalisePath xs
normalisePath (".." :: xs) = normalisePath xs
normalisePath (x :: ".." :: xs) = normalisePath xs
normalisePath (x :: xs) = x :: normalisePath xs

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
pathForIO : Path -> String
pathForIO (Home xs) = "~/" ++ (addSlashes xs)
pathForIO (Absolute xs) = "/" ++ (addSlashes xs)
pathForIO (Relative xs) = (addSlashes xs)

public export
record FilePath where
  constructor MkFilePath
  path : Path
  fileName : Maybe String

public export
Show FilePath where
  show x = "(MkFilePath " ++ (show (path x)) ++ " " ++ (show (fileName x)) ++ ")"

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
filePathForIO (MkFilePath path Nothing) = pathForIO path
filePathForIO (MkFilePath path (Just x)) = (pathForIO path) ++ "/" ++ x
