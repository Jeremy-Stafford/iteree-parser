module Text.Iteree.Char

import Data.String
import Data.String.Iterator

import Text.Iteree.Combinators
import Text.Iteree.Types

||| Parse a single character
export
char : Char -> Parser Char Char
char = token1

||| Parse a list of characters
listChars : String -> List Char -> Parser Char (List Char)
listChars _ [] = MkParser
    { result = \pos => Right []
    , next = \pos, c => Left $ Unexpected (Just c) neutral
    }
listChars str (c :: cs) = MkParser
    { result = \_ => Left $ unexpected1 Nothing (Named str)
    , next = \pos, c' => if c == c'
        then Right $ (c ::) <$> listChars str cs
        else Left $ unexpected1 (Just c') (Named str)
    }

||| Parse a string
||| @ expected the expected string
export
string : (expected : String) -> Parser Char String
string str = map fastPack $ listChars str $ fastUnpack str

partial
toNatDigitD : Num a => Char -> a
toNatDigitD = \case
    '0' => 0
    '1' => 1
    '2' => 2
    '3' => 3
    '4' => 4
    '5' => 5
    '6' => 6
    '7' => 7
    '8' => 8
    '9' => 9

||| Parse a decimal.
export
decimal : Num a => Parser Char a
decimal = label "decimal" $ foldl (\acc, d => acc * 10 + (assert_total $ toNatDigitD d)) 0 <$> takeWhile isDigit

partial
toNatDigitH : Num a => Char -> a
toNatDigitH = \case
    '0' => 0
    '1' => 1
    '2' => 2
    '3' => 3
    '4' => 4
    '5' => 5
    '6' => 6
    '7' => 7
    '8' => 8
    '9' => 9
    'a' => 0xa
    'b' => 0xb
    'c' => 0xc
    'd' => 0xd
    'e' => 0xe
    'f' => 0xf

||| Parse a hexadecimal.
export
hexadecimal : Num a => Parser Char a
hexadecimal = label "hex" $ foldl (\acc, d => acc * 16 + (assert_total $ toNatDigitH d)) 0 <$> takeWhile isHexDigit

||| Parse a signed integer
export
signed : Neg a => Parser Char a -> Parser Char a
signed p = p
    <|> char '+' *> p
    <|> char '-' *> negate <$> p

||| Parse a float
export
fractional : Fractional a => Parser Char a
fractional = go tenth <$> decimal <* char '.' <*> takeWhile isDigit
  where
    tenth : a
    tenth = 1 / 10
    go : a -> a -> List Char -> a
    go exp acc [] = acc
    go exp acc (d :: ds) = go (exp * tenth) (acc + assert_total (toNatDigitD d) * exp) ds