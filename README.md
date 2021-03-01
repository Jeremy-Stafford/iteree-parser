# iteree-parser
An iteree-based monadic parser combinator library in Idris.

# Running parsers
A parser can be run on a list of tokens
```idris example
> runParser (token True) [True]
Right True
```

There are specialised versions for use with strings (where tok = Char)
