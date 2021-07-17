module Idrall.TestHelper

import Idrall.Error
import Idrall.IOEither
import Idrall.APIv1
import Idrall.Value

import System
import System.Directory
import System.Path
import System.Directory.Tree

import Data.List
import Data.String
import Data.String.Extra

public export
record Result where
  constructor MkResult
  pass : Nat
  fail : Nat

public export
Show Result where
  show (MkResult pass fail) = "Result: " ++ "\n" ++
                              "Pass: " ++ show pass ++ "\n" ++
                              "Fail: " ++ show fail

public export
Semigroup Result where
  (<+>) (MkResult pass fail) (MkResult pass' fail') = MkResult (pass + pass') (fail + fail')

public export
Monoid Result where
  neutral = MkResult 0 0

-- TODO open idris2 PR?
foldlMapM : (Foldable g, Monoid b, Applicative m) => (a -> m b) -> g a -> m b
foldlMapM f = foldr f' (pure neutral)
  where
  f' : a -> m b -> m b
  f' x y = liftA2 (<+>) (f x) y

mkres : IOEither Error a -> IO Result
mkres (MkIOEither x) = do
  x' <- x
  case x' of
       (Left y) => do
         printLn y
         pure (MkResult 0 1)
       (Right y) => pure (MkResult 1 0)

data TestPair
  = MkTestPair String String

Show TestPair where
  show (MkTestPair a b) = a ++ " : " ++ b

fileNameAB : {root : _} -> FileName root -> TestPair
fileNameAB a =
  let fileA = show $ toFilePath a
      fileB = aToB fileA
  in do
    MkTestPair fileA fileB
  where
    aToB : String -> String
    aToB a = (dropLast 7 a) ++ "B.dhall" -- 7 chars in "A.dhall"

-- filters
matchFiles : {root : _} -> List String -> FileName root -> Bool
matchFiles [] n = False
matchFiles (x :: xs) n =
  case isInfixOf x (fileName n) of
       False => matchFiles xs n
       True => True

defaultFilters : List ({root : _} -> FileName root -> Bool)
defaultFilters = [findAFiles]
  where
    findAFiles : {root : _} -> FileName root -> Bool
    findAFiles x =
      let fileNameStr = fileName x in
        isSuffixOf "A.dhall" fileNameStr

runTests' : (path : String)
          -> (String -> String -> IOEither Error a)
          -> (filters : List ({root : _} -> FileName root -> Bool))
          -> IO Result
runTests' path f filters =
  let dir = explore $ parse path
      testFiles = doFilter filters !dir
  in do
    res <- depthFirst doTest (sort testFiles) $ pure neutral
    pure res
    where
    runTestPair : TestPair -> (String -> String -> IOEither Error a) -> IOEither Error a
    runTestPair (MkTestPair a b) f = f a b
    doTest : {root : _} -> FileName root -> Lazy (IO Result) -> IO Result
    doTest x next = do
      putStrLn $ "Testing: \{show $ toFilePath x}"
      res <- mkres $ runTestPair (fileNameAB x) f
      pure $ res <+> !next
    doFilter : {root : _}
             -> List ({root : _} -> FileName root -> Bool)
             -> Tree root
             -> Tree root
    doFilter [] x = x
    doFilter (f :: xs) x =
      doFilter xs (System.Directory.Tree.filter f (\_ => True) x)

public export
runTests : (path : String) -> (String -> String -> IOEither Error a) -> IO Result
runTests path f = runTests' path f defaultFilters

public export
runTestsOnly : (onlyList : List String) -> (path : String) -> (String -> String -> IOEither Error a) -> IO Result
runTestsOnly onlyList path f = runTests' path f ((matchFiles onlyList) :: defaultFilters)

public export
ppResult : Result -> String
ppResult (MkResult pass fail) =
  """
  Result:
  Pass: \{show pass}
  Fail: \{show fail}
  """
