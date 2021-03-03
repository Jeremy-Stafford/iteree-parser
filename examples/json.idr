import Data.String
import Language.JSON.Data

import Text.Iteree
import Text.Iteree.Char

lexeme : Parser Char a -> Parser Char a
lexeme = skip (token isSpace)

symbol : String -> Parser Char String
symbol = lexeme . string

quotedString : Parser Char String
quotedString = lexeme $ fastPack <$> between (char '"') (char '"') (takeWhile (/= '"'))

bool : Parser Char Bool
bool = True <$ symbol "true" <|> False <$ symbol "false"

mutual
    array : Parser Char (List JSON)
    array = between (symbol "[") (symbol "]") $ json `sepBy` symbol ","

    json : Parser Char JSON
    json = JNull <$ string "null"
        <|> JBoolean <$> bool
        <|> JArray <$> array


source : String
source = "ADSSDA"

main : IO ()
main = do
    let Right res = runParserString json source
        | Left err => putStrLn $ prettyParseError err
    printLn res

