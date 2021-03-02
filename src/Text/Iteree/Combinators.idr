module Text.Iteree.Combinators

import Data.Either
import Data.List
import Data.List1
import Data.SortedSet

import Text.Iteree.Types

%hide Data.List.NonEmpty

{-
===============================================================================
Error combinators
===============================================================================
-}

||| Label a parser with a name to improve error messages.
export
label : String -> Parser tok a -> Parser tok a
label lbl p =
    let e = \t => unexpected1 t $ Named lbl
    in MkParser
        { result = \pos => mapFst (const $ e Nothing) $ p.result pos
        , next = \pos, t => mapFst (const $ e $ Just t) $ p.next pos t
        }

||| Label a parser with many tokens to improve error messages.
export
labels : List tok -> Parser tok a -> Parser tok a
labels ts p =
    let e = \t => Unexpected t (map Token ts)
    in MkParser
        { result = \pos => mapFst (const $ e Nothing) $ p.result pos
        , next = \pos, t => mapFst (const $ e $ Just t) $ p.next pos t
        }

||| Hide an error message
export
hidden : Parser tok a -> Parser tok a
hidden p = MkParser
    { result = \pos => mapFst hideError $ p.result pos
    , next = \pos, t => bimap hideError hidden $ p.next pos t
    }
  where
    hideError : RawParseError tok -> RawParseError tok
    hideError (Unexpected t ts) = Unexpected t neutral

{-
===============================================================================
Parser combinators
===============================================================================
-}

||| Remove a parser's ability to accept the empty input.
export
nonEmpty : Parser tok a -> Parser tok a
nonEmpty p = MkParser
    { result = \_ => Left $ Unexpected Nothing neutral
    , next = p.next
    }

mutual
    ||| Parse any number of occurances of `p`.
    ||| @ p parser to repeat
    export
    many : (p : Parser tok a) -> {auto 0 prf : NonEmpty p} -> Parser tok (List a)
    many p = some p <|> pure []

    ||| Parse one or more occurances of `p`.
    export
    some : (p : Parser tok a) -> {auto 0 prf : NonEmpty p} -> Parser tok (List a)
    some p = [| p :: many p |]

||| Parser one or more occurances of `p`.
export
some1 : (p : Parser tok a) -> {auto 0 prf : NonEmpty p} -> Parser tok (List1 a)
some1 p = [| p ::: many p |]

export
||| Run `p` between `left` and `right`.
between : (left : Parser tok _) -> (right : Parser tok _) -> (p : Parser tok a) -> Parser tok a
between left right p = left *> p <* right

{-
===============================================================================
Token-based parsers
===============================================================================
-}

||| Parse a token satisfying a predicate.
export
token : (pred : tok -> Bool) -> Parser tok tok
token pred = MkParser
    { result = \_ => Left $ Unexpected Nothing neutral
    , next = \_, t => if pred t
        then Right $ pure t
        else Left $ Unexpected (Just t) neutral
    }

||| Parse a single token.
export
token1 : Eq tok => tok -> Parser tok tok
token1 t = labels [t] $ token (t ==)

||| Parse any number of tokens satisfying `pred`
export
takeWhile : (pred : tok -> Bool) -> Parser tok (List tok)
takeWhile pred = MkParser
    { result = \_ => Right []
    , next = \_, t => if pred t
        then Right $ map (t ::) (takeWhile pred)
        else Left $ Unexpected (Just t) neutral
    }

||| Parse one or more tokens satisfying `pred`
export
takeWhile1 : (pred : tok -> Bool) -> Parser tok (List tok)
takeWhile1 pred = nonEmpty $ takeWhile pred

||| Optionally run a parser
export
optional : Parser tok a -> Parser tok (Maybe a)
optional p = Just <$> p <|> pure Nothing