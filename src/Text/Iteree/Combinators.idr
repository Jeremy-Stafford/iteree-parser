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

||| Hide an error message.
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

||| Give a parser the ability to accept empty input.
||| 
||| Laws:
||| 
||| ```idris example
||| nonEmpty (optional p) = map Just p
||| optional (nonEmpty p) = pure Nothing <|> map Just p 
||| ```
export
optional : Parser tok a -> Parser tok (Maybe a)
optional p = map Just p <|> pure Nothing

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

||| Run `p` between `left` and `right`.
export
between : (left : Parser tok _) -> (right : Parser tok _) -> (p : Parser tok a) -> Parser tok a
between left right p = left *> p <* right

||| Skip any number of occurences of the first parser, then parse the second.
|||
||| For a version which skips exactly one occurence, use `(*>)`.
export
skip : (ignore : Parser tok _) -> {auto 0 prf : NonEmpty ignore} -> Parser tok a -> Parser tok a
skip ignore p = many ignore *> p

export
skipIsNonEmpty : {auto 0 prf1 : NonEmpty ignore} -> {auto 0 prf2 : NonEmpty p} -> NonEmpty (skip ignore {prf = prf1} p)
skipIsNonEmpty = IsNonEmpty \_ => ItIsLeft

||| Parse at least one occurence of `item`, seperated by `sep`.
export
sepBy1 :
    (item : Parser tok a) ->
    (sep : Parser tok _) ->
    {auto 0 prf : Either (NonEmpty item) (NonEmpty sep)} ->
    Parser tok (List a)
sepBy1 item sep = (::) <$> item <*> (pure [] <|> sep *> sepBy1 item sep)

||| Parse any number of occurences of `item`, seperated by `sep`.
export
sepBy :
    (item : Parser tok a) ->
    (sep : Parser tok _) ->
    {auto 0 prf : Either (NonEmpty item) (NonEmpty sep)} ->
    Parser tok (List a)
sepBy item sep = pure [] <|> sepBy1 item sep

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

||| A proof that any parser built with `token` is non-empty.
export
tokenIsNonEmpty : NonEmpty (token pred)
tokenIsNonEmpty = IsNonEmpty \_ => ItIsLeft

||| Parse a single token.
export
token1 : Eq tok => tok -> Parser tok tok
token1 t = labels [t] $ token (t ==)

||| Parse any number of tokens satisfying `pred`.
export
takeWhile : (pred : tok -> Bool) -> Parser tok (List tok)
takeWhile pred = MkParser
    { result = \_ => Right []
    , next = \_, t => if pred t
        then Right $ map (t ::) (takeWhile pred)
        else Left $ Unexpected (Just t) neutral
    }

||| Parse one or more tokens satisfying `pred`.
export
takeWhile1 : (pred : tok -> Bool) -> Parser tok (List tok)
takeWhile1 pred = nonEmpty $ takeWhile pred

{-
===============================================================================
Lexers
===============================================================================
-}

lex : Show tok2 => Parser tok1 tok2 -> Parser tok2 a -> Parser tok1 a
lex lexer parser = MkParser
    { result = mapFst mapError . parser.result
    , next = \pos, c => case lexer.next pos c of
        Left e => Left e
        Right lexer' =>
            let lex' = lex lexer' parser
            in case lexer'.result pos of
                Left e => Right lex'
                Right t => case parser.next pos t of
                    Left e => Right lex'
                    Right parser' => Right $ lex' <|> lex lexer parser'
    }
  where
    mapError : RawParseError tok2 -> RawParseError tok1
    mapError (Unexpected t ts) =
        Unexpected Nothing $
            (\case
                Token t => Named $ show t
                Named s => Named s    
            ) <$> ts