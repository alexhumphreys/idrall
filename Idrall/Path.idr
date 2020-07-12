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

record FilePath where
  constructor MkFilePath
  fileName : String
  dir : Dir

public export
getFile : Dir -> (List String, Maybe String)
getFile [] = ([], Nothing)
getFile [x] = ([], Just x)
getFile (x :: xs) =
  let (dir, file) = getFile xs in
      (x :: dir, file)

filePathFromPath : Path -> FilePath
filePathFromPath (Home xs) = ?filePathFromPath_rhs_1
filePathFromPath (Absolute xs) = ?filePathFromPath_rhs_2
filePathFromPath (Relative xs) = ?filePathFromPath_rhs_3
