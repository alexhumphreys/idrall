module Main

import Idrall.TestHelper

import Idrall.Error
import Idrall.IOEither
import Idrall.APIv1
import Idrall.Parser

import System
import System.Directory
import Data.List
import Data.Strings
import Data.Strings

record DirTree a where
  constructor MkDirTree
  path : String
  dirs : List (DirTree a)
  cases : List a

record Result where
  constructor MkRecord
  pass : Nat
  fail : Nat

Show (DirTree String) where
  show x = show (path x) ++ "\n" ++ show (cases x) ++ "\n" ++ show (dirs x)

Show Result where
  show (MkRecord pass fail) = "Pass: " ++ show pass ++ "\n" ++
                              "Fail: " ++ show fail

Semigroup Result where
  (<+>) (MkRecord pass fail) (MkRecord pass' fail') = MkRecord (pass + pass') (fail + fail')

Monoid Result where
  neutral = MkRecord 0 0

Foldable DirTree where
  foldr f init (MkDirTree str ds cs) =
    let casesRes = foldr f init cs
        dirsRes = foldr (\x => \y => foldr f y x) casesRes ds
    in
    dirsRes

findd : String -> IO (DirTree String)
findd x = do
  dh <- openDir x
  case dh of
       (Left er) => do putStrLn $ "couldn't open dir " ++ x ; exitFailure
       (Right d) => do
         entries <- listDir d []
         dirs <- getDirs x entries
         let cases = stripSuffix <$> (onlyA (sort entries))
         dirTrees <- sequence $ map findd dirs
         pure $ MkDirTree x dirTrees cases

-- roundTripCheck : String -> String -> IOEither Error ()

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

runTest : (String, String) -> IO Result
runTest x =
  let x' = nameCases x in do
        putStrLn $ "Testing: " ++ show x
        mkres $ roundTripCheck (fst x') (snd x')

runTests : DirTree String -> IO Result
runTests x =
  let x' = decorate x in
      foldlMapM {g=DirTree} {b=Result} {m=IO} runTest x'

testAll : IO (Result)
testAll = do
  dir <- findd "../../../dhall-lang/tests/type-inference/success"
  runTests dir

main : IO ()
main = do res <- testAll
          printLn $ res
