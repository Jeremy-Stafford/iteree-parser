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

{-
||| Parse a decimal.
export
decimal : Parser Char Nat
decimal = label "decimal" $ assert_total toNat <$> takeWhile1C isDigit
  where
    partial
    toNatDigit : Char -> Nat
    toNatDigit '0' = 0
    toNatDigit '1' = 1
    toNatDigit '2' = 2
    toNatDigit '3' = 3
    toNatDigit '4' = 4
    toNatDigit '5' = 5
    toNatDigit '6' = 6
    toNatDigit '7' = 7
    toNatDigit '8' = 8
    toNatDigit '9' = 9

    partial
    toNatIt : Nat -> {str : String} -> (1 _ : StringIterator str) -> Nat
    toNatIt acc {str} it = case uncons str it of
        EOF => 0
        Character c it' => toNatDigit c

    partial
    toNat : String -> Nat
    toNat s = withString s (toNatIt 0)

export
signedDecimal : Parser Char Integer
signedDecimal =
    char '-' *> (negate . cast) <$> decimal
    <|> char '+' *> cast <$> decimal
    <|> cast <$> decimal
-}
