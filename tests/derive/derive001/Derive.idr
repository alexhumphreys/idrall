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

record ExRec1 where
  constructor MkExRec1
  mn : Maybe Nat
  n : Nat
  i : Integer
  b : Bool
  d : Double
  lb : List Bool
  st : String
  mst : Maybe String
  -- a6 : Nat

Show ExRec1 where
  show (MkExRec1 mn n i b d lb st mst) =
    "(MkExample3 \{show mn} \{show n} \{show i} \{show b} \{show d} \{show lb} \{show st} \{show mst})"

%runElab (deriveFromDhall Record `{{ ExRec1 }})

exRec1 : Maybe ExRec1
exRec1 = fromDhall
  (ERecordLit $
    fromList [ (MkFieldName "mn", ENaturalLit 3)
             , (MkFieldName "n", ENaturalLit 4)
             , (MkFieldName "i", EIntegerLit 5)
             , (MkFieldName "b", EBoolLit True)
             , (MkFieldName "d", EDoubleLit 2.0)
             , (MkFieldName "lb", EListLit (Just EBool) [EBoolLit True, EBoolLit False])
             , (MkFieldName "st", (ETextLit (MkChunks [] "hello")))
             , (MkFieldName "mst", (ETextLit (MkChunks [] "hello")))
             ])

data ExADT1
  = Foo
  | Bar Bool
  | Baz (Maybe Bool)

Show ExADT1 where
  show Foo = "Foo"
  show (Bar x) = "(Bar \{show x})"
  show (Baz x) = "(Baz \{show x})"

%runElab (deriveFromDhall ADT `{{ ExADT1 }})

exADT1 : Maybe ExADT1
exADT1 = fromDhall
  (EApp (EField (EUnion $ fromList []) (MkFieldName "Foo")) $ ENaturalLit 3)
exADT2 : Maybe ExADT1
exADT2 = fromDhall
  (EApp (EField (EUnion $ fromList []) (MkFieldName "Bar")) $ EBoolLit True)
exADT3 : Maybe ExADT1
exADT3 = fromDhall
  (EApp (EField (EUnion $ fromList []) (MkFieldName "Baz")) $ ESome $ EBoolLit True)

exADT4 : Maybe ExADT1
exADT4 = fromDhall
        (EApp (EField
          ( EUnion $ fromList
            [ ((MkFieldName "Bar"), Just EBool)
            , ((MkFieldName "Foo"), Just ENatural)
            ]
          ) (MkFieldName "Foo")) (ENaturalLit 3))

putLines : Show a => List a -> IO ()
putLines = putStrLn . fastAppend . (intersperse "\n") . map show

main : IO ()
main = do putLines [exRec1]
          putLines [exADT1, exADT2, exADT3, exADT4]
