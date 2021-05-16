module Main

import Idrall.TestHelper

import Idrall.Expr
import Idrall.APIv1
import Idrall.Derive

import System.Directory
import Data.List
import Data.Strings
import Language.Reflection

%language ElabReflection

record Example3 where
  constructor MkExample3
  mn : Maybe Nat
  n : Nat
  i : Integer
  b : Bool
  lb : List Bool
  -- a6 : Nat

Show Example3 where
  show (MkExample3 mn n i b lb) =
    "(MkExample3 \{show mn} \{show n} \{show i} \{show b} \{show lb})"

%runElab (deriveFromDhall `{{ Example3 }})

bar3 : Maybe Example3
bar3 = fromDhall
  (ERecordLit $
    fromList [ (MkFieldName "mn", ENaturalLit 3)
             , (MkFieldName "n", ENaturalLit 4)
             , (MkFieldName "i", EIntegerLit 5)
             , (MkFieldName "b", EBoolLit True)
             , (MkFieldName "lb", EListLit (Just EBool) [EBoolLit True, EBoolLit False])
             -- , (MkFieldName "a7", EBoolLit True)
             ])

main : IO ()
main = do printLn $ show bar3
