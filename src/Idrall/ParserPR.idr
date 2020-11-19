module Idrall.ParserPR

import Control.Monad.Identity
import Control.Monad.Trans

import Data.Fin
import Data.Nat
import Data.Strings
import Data.Vect
import Data.List1
import Data.String.Parser

public export
sepBy1 : Monad m => (p : ParseT m a)
                 -> (s : ParseT m b)
                 -> ParseT m (List a)
sepBy1 p s = [| p :: many (s *> p) |]

public export
sepBy : Monad m => (p : ParseT m a)
                -> (s : ParseT m b)
                -> ParseT m (List a)
sepBy p s = (p `sepBy1` s) <|> pure []

public export
||| Parses /one/ or more occurrences of `p` separated by `comma`.
commaSep1 : Monad m => ParseT m a -> ParseT m (List a)
commaSep1 p = p `sepBy1` (char ',')

public export
||| Parses /zero/ or more occurrences of `p` separated by `comma`.
commaSep : Monad m => ParseT m a -> ParseT m (List a)
commaSep p = p `sepBy` (char ',')

public export
ntimes : Monad m => (n : Nat) -> ParseT m a -> ParseT m (Vect n a)
ntimes    Z  p = pure Vect.Nil
ntimes (S n) p = [| p :: (ntimes n p) |]

public export
alphaNum : Monad m => ParseT m Char
alphaNum = satisfy isAlphaNum <?> "letter or digit"

public export
letter : Monad m => ParseT m Char
letter = satisfy isAlpha <?> "letter"

reverseResult : State -> Result a -> Result ()
reverseResult s@(S input pos maxPos) (Fail x y) = OK () s
reverseResult s@(S input pos maxPos) (OK x y) = Fail maxPos "Purposfully changed OK to Fail" -- not sure about maxPos

public export
requireFailure : Monad m => (p : ParseT m a)
                         -> ParseT m ()
requireFailure (P runParser) = P rev
where
  rev : State -> m (Result ())
  rev s@(S input pos maxPos) = do
    res <- runParser s
    pure (reverseResult s res)
