module Idrall.TestHelper

import Idrall.Error
import Idrall.IOEither
import Idrall.APIv1
import Idrall.Value

import System
import System.Directory
import Data.List
import Data.Strings

public export
record DirTree a where
  constructor MkDirTree
  path : String
  dirs : List (DirTree a)
  cases : List a

public export
record Result where
  constructor MkRecord
  pass : Nat
  fail : Nat

public export
Show (DirTree String) where
  show x = show (path x) ++ "\n" ++ show (cases x) ++ "\n" ++ show (dirs x)

public export
Show Result where
  show (MkRecord pass fail) = "Result: " ++ "\n" ++
                              "Pass: " ++ show pass ++ "\n" ++
                              "Fail: " ++ show fail

public export
Semigroup Result where
  (<+>) (MkRecord pass fail) (MkRecord pass' fail') = MkRecord (pass + pass') (fail + fail')

public export
Monoid Result where
  neutral = MkRecord 0 0

public export
Foldable DirTree where
  foldr f init (MkDirTree str ds cs) =
    let casesRes = foldr f init cs
        dirsRes = foldr (\x => \y => foldr f y x) casesRes ds
    in
    dirsRes

listDir : Directory -> List String -> IO (List String)
listDir d  ls = do
  dx <- dirEntry d
  case dx of
    Left  de => pure ls         --no more entries, return the list
    Right sn => listDir d (sn :: ls)

stripSuffix : String -> String
stripSuffix x =
  let revX = reverse x
      listX = unpack revX
      rest = drop 7 listX
  in
  pack (reverse rest)

onlyA : List String -> List String
onlyA xs = filter (isSuffixOf "A.dhall") xs

dirExists : String -> IO Bool
dirExists dir = do
  Right d <- openDir dir
    | Left _ => pure False
  closeDir d
  pure True

getDirs : String -> List String -> IO (List String)
getDirs path ls = do x <- go path ls
                     pure $ sort x
where
  go : String -> List String -> IO (List String)
  go path [] = pure []
  go path ("." :: xs) = go path xs
  go path (".." :: xs) = go path xs
  go path (x :: xs) = do
    exists <- dirExists $ (path ++ "/" ++ x)
    case exists of
         True => pure $ (path ++ "/" ++ x) :: !(go path xs)
         False => go path xs

public export
findTests : String -> IO (DirTree String)
findTests x = do
  dh <- openDir x
  case dh of
       (Left er) => do putStrLn $ "couldn't open dir " ++ x ; exitFailure
       (Right d) => do
         entries <- listDir d []
         dirs <- getDirs x entries
         let cases = stripSuffix <$> (onlyA (sort entries))
         dirTrees <- sequence $ map findTests dirs
         pure $ MkDirTree x dirTrees cases

-- TODO open idris2 PR?
foldlMapM : (Foldable g, Monoid b, Applicative m) => (a -> m b) -> g a -> m b
foldlMapM f = foldr f' (pure neutral)
  where
  f' : a -> m b -> m b
  f' x y = liftA2 (<+>) (f x) y

decorate : DirTree a -> DirTree (String, a) -- TODO use path
decorate (MkDirTree path ds cs) =
  MkDirTree path (map decorate ds) (map (\c=> (path, c)) cs)

mkres : IOEither Error () -> IO Result
mkres (MkIOEither x) = do
  x' <- x
  case x' of
       (Left y) => do
         printLn y
         pure (MkRecord 0 1)
       (Right y) => pure (MkRecord 1 0)

nameCases : (String, String) -> (String, String)
nameCases (path, c) = (path ++ "/" ++ c ++ "A.dhall", path ++ "/" ++ c ++ "B.dhall")

runTestAB : (String, String) -> (String -> String -> IOEither Error ()) -> IO Result
runTestAB x f =
  let x' = nameCases x in do
        putStrLn $ "Testing: " ++ show x
        mkres $ f (fst x') (snd x')

runTests : DirTree String -> ((String, String) -> IO Result) -> IO Result
runTests x h =
  let x' = decorate x in
      foldlMapM {g=DirTree} {b=Result} {m=IO} h x'

runFormatter : (String -> String -> IOEither Error ()) -> (String, String) -> IO Result
runFormatter f x = runTestAB x f

public export
runTestsCheck : DirTree String -> IO Result
runTestsCheck x = runTests x (runFormatter roundTripCheck)

public export
runTestsConv : DirTree String -> IO Result
runTestsConv x = runTests x (runFormatter roundTripEvalQuoteConv)
