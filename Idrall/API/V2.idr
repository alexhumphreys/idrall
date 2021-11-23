module Idrall.API.V2

import Idrall.Value
import public Idrall.Expr
import public Idrall.Error
import public Idrall.Derive
import public Idrall.Derive.ToDhall
import public Idrall.IOEither
import Idrall.APIv1

import System.Path -- TODO make public export in System.Directory.Tree?

export
deriveFromDhallString : FromDhall ty => String -> IOEither Error ty
deriveFromDhallString x = do
  e <- roundTripCheckEvalQuote $ x
  liftEither $ fromDhall e

export
deriveFromDhallFile : FromDhall a => Path -> IOEither Error a
deriveFromDhallFile = deriveFromDhallString . show
