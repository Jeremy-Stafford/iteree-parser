import Text.Iteree
import Text.Iteree.Char


assertEq : Eq a => String -> a -> a -> IO ()
assertEq name x y = if x == y
    then putStrLn $ "passed " <+> name
    else putStrLn $ "failed " <+> name

main : IO ()
main = do
    let Right n = runParserString decimal "12345"
        | Left err => putStrLn $ prettyParseError err
    assertEq "decimal" n 12345

    let Right n = runParserString hexadecimal "123abc"
        | Left err => putStrLn $ prettyParseError err
    assertEq "hexadecimal" n 0x123abc

    let Right n = runParserString fractional "123.456"
        | Left err => putStrLn $ prettyParseError err
    assertEq "fractional" n 123.456

    pure ()
