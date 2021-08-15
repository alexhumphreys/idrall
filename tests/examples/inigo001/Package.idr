module Main

import Idrall.APIv1

main : IO ()
main = do
  expr <- liftIOEither $ roundTripSynthEvalQuote "./Inigo.dhall"
  putStrLn $ show expr
