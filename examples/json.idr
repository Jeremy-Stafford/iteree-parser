import Data.String
import Language.JSON.Data

import Text.Iteree
import Text.Iteree.Char

quotedString : Parser Char String
quotedString = fastPack <$> between (char '"') (char '"') (takeWhile (/= '"'))


bool : Parser Char Bool
bool = True <$ string "true" <|> False <$ string "false"

pJson : Parser Char JSON
pJson = JNull <$ string "null"
    <|> JBoolean <$> bool


source : String
source = "ADSSDA"

main : IO ()
main = do
    let Right json = runParserString pJson source
        | Left err => putStrLn "error"
    printLn json

