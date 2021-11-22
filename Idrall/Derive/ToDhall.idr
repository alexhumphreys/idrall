module Idrall.Derive.ToDhall

import Idrall.Expr
import Idrall.Error
import Idrall.Pretty

import public Data.SortedMap
import Text.PrettyPrint.PrettyPrinter.Render.Terminal

public export
interface ToDhall ty where
  toDhallType : Either Error (Expr Void)
  toDhall : ty -> Either Error (Expr Void)

export
ToDhall Nat where
  toDhallType = Right $ ENatural EmptyFC
  toDhall x = Right $ ENaturalLit EmptyFC x

export
ToDhall Bool where
  toDhallType = Right $ EBool EmptyFC
  toDhall x = Right $ EBoolLit EmptyFC x

export
ToDhall Integer where
  toDhallType = Right $ EInteger EmptyFC
  toDhall x = Right $ EIntegerLit EmptyFC x

export
ToDhall Double where
  toDhallType = Right $ EDouble EmptyFC
  toDhall x = Right $ EDoubleLit EmptyFC x

export
ToDhall String where
  toDhallType = Right $ EText EmptyFC
  toDhall x = Right $ ETextLit EmptyFC (MkChunks [] x)

export
ToDhall ty => ToDhall (List ty) where
  toDhallType = Right $ EApp EmptyFC (EList EmptyFC) !(toDhallType {ty=ty})
  toDhall xs = Right $ EListLit EmptyFC (Just !(toDhallType {ty=ty})) !(traverse toDhall xs)

export
ToDhall ty => ToDhall (Maybe ty) where
  toDhallType = Right $ EApp EmptyFC (EOptional EmptyFC) !(toDhallType {ty=ty})
  toDhall Nothing = Right $ EApp EmptyFC (ENone EmptyFC) !(toDhallType {ty=Maybe ty})
  toDhall (Just x) = Right $ ESome EmptyFC !(toDhall x)

export
Pretty Void where
  pretty x = pretty ""

testPretty : ToDhall ty => ty -> IO ()
testPretty x =
  let dhall = toDhall x
  in case dhall of
          (Left y) => do
            putStrLn $ show y
          (Right y) => do
            putDoc $ pretty y
