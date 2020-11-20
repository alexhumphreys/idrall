module Idrall.Lexer

import Control.Monad.Identity
import Control.Monad.Trans

import Data.Vect
import Data.List
import Data.Nat
import Data.String.Parser

import Idrall.ParserPR

-- Not a real Lexer, more a collection of small parsing utilities.

public export
hexNumber : Parser Int
hexNumber = choice (the (List (Parser Int)) [ hexDigit, hexUpper, hexLower ])
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
  char 'u'
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
    char '{'
    ns <- some hexNumber
    guard (validCodepoint (toNumber ns)
          && (toNumber ns) <= 0x10fffd) -- TODO use let with idris2 to DRY
          <|> fail "Invalid Unicode code point"
    char '}'
    pure (toNumber ns)
