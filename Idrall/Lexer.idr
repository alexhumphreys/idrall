module Idrall.Lexer

import Control.Monad.Identity
import Control.Monad.Trans

import Data.Vect
import Data.List
import Data.Nat
import Data.String.Parser
import Data.String
import Data.List1

-- Not a real Lexer, more a collection of small parsing utilities.

export
commaSep1' : Monad m => ParseT m a -> ParseT m (List1 a)
commaSep1' p = p `sepBy1` (token ",")

mutual
  blockCommentChunk : Parser String
  blockCommentChunk =
    blockComment <|> characters <|> character <|> endOfLine
    where
      characters : Parser String
      characters = (takeWhile1 predicate)
        where
          predicate : Char -> Bool
          predicate c =
                  '\x20' <= c && c <= '\x10FFFF' && c /= '-' && c /= '{'
              ||  c == '\n'
              ||  c == '\t'

      character : Parser String
      character = do x <- satisfy predicate
                     pure $ singleton x
        where
          predicate : Char -> Bool
          predicate c = '\x20' <= c && c <= '\x10FFFF' || c == '\n' || c == '\t'

      endOfLine : Parser String
      endOfLine = (string "\r\n" <?> "newline")

  blockCommentContinue : Parser String
  blockCommentContinue = endOfComment <|> continue
    where
      endOfComment : Parser String
      endOfComment = token "-}" *> pure ""

      continue : Parser String
      continue = do
          c <- blockCommentChunk
          c' <- blockCommentContinue
          pure (c <+> c')

  public export
  blockComment : Parser String
  blockComment = do
      _ <- string "{-"
      c <- blockCommentContinue
      pure c

public export
lineComment : Parser String
lineComment = token "--" *> takeWhile (\c => c /= '\n') <* token "\n"

public export
whitespace : Parser ()
whitespace =  skip blockComment <|> skip (some lineComment) <|> spaces

public export
hexNumber : Parser Int
hexNumber = choice (the (List (Lazy (Parser Int))) [ hexDigit, hexUpper, hexLower ])
where
  hexDigit : Parser Int
  hexDigit = do
    c <- satisfy (\c => '0' <= c && c <= '9')
    pure (ord c - ord '0') -- TODO understand this
  hexUpper : Parser Int
  hexUpper = do
    c <- satisfy (\c => 'A' <= c && c <= 'F')
    pure (10 + ord c - ord 'A')
  hexLower : Parser Int
  hexLower = do
    c <- satisfy (\c => 'a' <= c && c <= 'f')
    pure (10 + ord c - ord 'a')

-- https://unicodebook.readthedocs.io/unicode_encodings.html#utf-16-surrogate-pairs
public export
isSurrogate : Int -> Bool
isSurrogate x =
  ((0xD800 <= x) && (x <= 0xDBFF))
    || ((0xDC00 <= x) && (x <= 0xDFFF))

{- TODO fix when idris2 has `Bits`
public export
bitAnd : Int -> Int -> Bits 1
bitAnd x y = and (cast (toInteger x)) (cast (toInteger y))
where
  toInteger : Int -> Integer
  toInteger x = cast x
  -}

public export
validCodepoint : Int -> Bool
validCodepoint c = not (isSurrogate c
                       --  TODO fix when idris2 has `Bits`
                       || True -- (bitsToInt (bitAnd c 0xFFFE)) == 0xFFFE
                       || True) -- (bitsToInt (bitAnd c 0xFFFF)) == 0xFFFF)

public export
unicode : Parser Char
unicode = do
  _ <- char 'u'
  n <- bracedEscapeSequence <|> fourCharacterEscapeSequence
  pure (chr n)
where
  toNumber : List Int -> Int
  toNumber = foldl (\x,y => x * 16 + y) 0
  vectToList : Vect m a -> List a
  vectToList [] = []
  vectToList (y :: xs) = y :: toList xs
  fourCharacterEscapeSequence : Parser Int
  fourCharacterEscapeSequence = do
    ns <- ntimes 4 hexNumber
    guard (validCodepoint (toNumber (vectToList ns))) -- TODO use let with idris2 to DRY
      <|> fail "Invalid Unicode code point"
    pure (toNumber (vectToList ns))
  bracedEscapeSequence : Parser Int
  bracedEscapeSequence = do
    _ <- char '{'
    ns <- some hexNumber
    guard (validCodepoint (toNumber ns)
          && (toNumber ns) <= 0x10fffd) -- TODO use let with idris2 to DRY
          <|> fail "Invalid Unicode code point"
    _ <- char '}'
    pure (toNumber ns)
