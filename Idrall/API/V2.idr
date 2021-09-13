module Idrall.API.V2

import Idrall.Value
import public Idrall.Expr
import public Idrall.Error
import public Idrall.Derive
import public Idrall.IOEither
import Idrall.APIv1

import System.Path -- TODO make public export in System.Directory.Tree?

liftMaybe : Maybe a -> IOEither Error a
liftMaybe Nothing = MkIOEither $ pure $ Left $ FromDhallError initFC "failed to convert from dhall"
liftMaybe (Just x) = pure x

export
deriveFromDhallString : FromDhall ty => String -> IOEither Error ty
deriveFromDhallString x = do
  e <- roundTripCheckEvalQuote $ x
  liftMaybe $ fromDhall e

export
deriveFromDhallFile : FromDhall a => Path -> IOEither Error a
deriveFromDhallFile = deriveFromDhallString . show
