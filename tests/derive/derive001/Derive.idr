module Main

import Idrall.TestHelper

import Idrall.Expr
import Idrall.API.V2

import System.Directory
import Data.List
import Data.String
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
  mst2 : Maybe String
  -- a6 : Nat

Show ExRec1 where
  show (MkExRec1 mn n i b d lb st mst mst2) =
    "(MkExample3 \{show mn} \{show n} \{show i} \{show b} \{show d} \{show lb} \{show st} \{show mst} \{show mst2})"

%runElab (deriveFromDhall Record `{ ExRec1 })

exRec1 : Maybe ExRec1
exRec1 = fromDhall
  (ERecordLit initFC $
    fromList [ (MkFieldName "mn", ESome initFC $ ENaturalLit initFC 3)
             , (MkFieldName "n", ENaturalLit initFC 4)
             , (MkFieldName "i", EIntegerLit initFC 5)
             , (MkFieldName "b", EBoolLit initFC True)
             , (MkFieldName "d", EDoubleLit initFC 2.0)
             , (MkFieldName "lb", EListLit initFC (Just $ EBool initFC) [EBoolLit initFC True, EBoolLit initFC False])
             , (MkFieldName "st", (ETextLit initFC (MkChunks [] "hello")))
             , (MkFieldName "mst", ESome initFC $ (ETextLit initFC (MkChunks [] "hello")))
             , (MkFieldName "mst2", (EApp initFC (ENone initFC) (EText initFC)))
             ])

data ExADT1
  = Foo
  | Bar Bool
  | Baz (Maybe Bool)

Show ExADT1 where
  show Foo = "Foo"
  show (Bar x) = "(Bar \{show x})"
  show (Baz x) = "(Baz \{show x})"

%runElab (deriveFromDhall ADT `{ ExADT1 })

exADT1 : Maybe ExADT1
exADT1 = fromDhall
  (EApp initFC (EField initFC (EUnion initFC $ fromList []) (MkFieldName "Foo")) $ ENaturalLit initFC 3)
exADT2 : Maybe ExADT1
exADT2 = fromDhall
  (EApp initFC (EField initFC (EUnion initFC $ fromList []) (MkFieldName "Bar")) $ EBoolLit initFC True)
exADT3 : Maybe ExADT1
exADT3 = fromDhall
  (EApp initFC (EField initFC (EUnion initFC $ fromList []) (MkFieldName "Baz")) $ ESome initFC $ EBoolLit initFC True)

exADT4 : Maybe ExADT1
exADT4 = fromDhall
        (EApp initFC (EField initFC
          ( EUnion initFC $ fromList
            [ ((MkFieldName "Bar"), Just $ EBool initFC)
            , ((MkFieldName "Foo"), Just $ ENatural initFC)
            ]
          ) (MkFieldName "Foo")) (ENaturalLit initFC 3))

putLines : Show a => List a -> IO ()
putLines = putStrLn . fastAppend . (intersperse "\n") . map show

main : IO ()
main = do putLines [exRec1]
          putLines [exADT1, exADT2, exADT3, exADT4]
