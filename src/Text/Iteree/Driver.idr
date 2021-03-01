module Text.Iteree.Driver

import Data.String.Iterator
import System.File

import Text.Iteree.Types

%default total

||| Consume a string iterator.
withoutIterator :
    (str : String) ->
    (1 it : StringIterator str) ->
    a ->
    a
withoutIterator str it a = withIteratorString str it (const a)

||| Add position information to an error.
withPos : Position -> RawParseError tok -> ParseError tok
withPos pos rawError = MkParseError { pos, rawError }

||| Advance a position a given character.
advanceChar : Char -> Position -> Position
advanceChar '\n' = record { line $= (+ 1), column = 1 }
advanceChar _ = record { column $= (+ 1) }

||| Run a parser on a list of tokens.
||| Returns the result of parsing or an error.
export
runParser :
    Parser tok a ->
    List tok ->
    {auto advance : Position -> tok -> Position} ->
    Either (ParseError tok) a
runParser p ts = go p ts pos1
  where
    go :
        Parser tok a ->
        List tok ->
        Position ->
        Either (ParseError tok) a
    go p ts pos = case ts of
        [] => mapFst (withPos pos) (p.result pos)
        (t :: ts') => mapFst (withPos pos) (p.next pos t) >>= \p' => go p' ts' (advance pos t)

partialRunString :
    Parser Char a ->
    String -> 
    Position ->
    Either (ParseError Char) (Position, Parser Char a)
partialRunString p str pos = withString str (go str p pos)
  where
    go :
        (str : String) ->
        Parser Char a ->
        Position ->
        (1 it : StringIterator str) ->
        Either (ParseError Char) (Position, Parser Char a)
    go str p pos it = case uncons str it of
        EOF => Right (pos, p)
        Character c it' => case p.next pos c of
            Left e => withoutIterator str it' (Left $ withPos pos e)
            Right p' => go str p' (advanceChar c pos) (assert_smaller it it') 

||| Run a `Char`-based parser on a string.
||| Returns the result of parsing or an error.
export
runParserString :
    Parser Char a ->
    String ->
    Either (ParseError Char) a
runParserString p str = partialRunString p str pos1 >>= \(pos, p') => mapFst (withPos pos) $ p'.result pos

||| Run a `Char`-based parser on a file, reading in chunks.
||| Returns the result of parsing or an error.
||| @ chunkSize number of characters to read at once.
export covering
runParserFile :
    HasIO io =>
    {default 1024 chunkSize : Int} ->
    Parser Char a ->
    (file : String) ->
    io $ Either FileError $ Either (ParseError Char) a
runParserFile p file = do
    Right f <- openFile file Read
        | Left err => pure $ Left err
    Right posp <- loop p f pos1
        | Left err => pure $ Left err
    pure $ Right $ posp >>= (\(pos, p') => mapFst (withPos pos) $ p'.result pos)
  where
    loop :
        Parser Char a ->
        File ->
        Position ->
        io $
            Either FileError $
                Either (ParseError Char)
                    (Position, Parser Char a)
    loop p f pos = do
        False <- fEOF f
            | True => pure $ Right $ Right (pos, p)
        Right str <- fGetChars f chunkSize
            | Left err => pure $ Left err
        let Right (pos', p') = partialRunString p str pos
            | Left err => pure $ Right $ Left err
        loop p' f pos'
