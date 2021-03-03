module Text.Iteree.Types

import Data.String

%default total

||| The position in the source.
public export
record Position where
    constructor MkPos
    line : Nat
    column : Nat

export
Eq Position where
    p1 == p2 = p1.line == p2.line && p1.column == p2.column

export
Ord Position where
    compare p1 p2 = compare p1.line p2.line <+> compare p1.column p2.column

export
pos1 : Position
pos1 = MkPos
    { line = 1
    , column = 1
    }

export
Cast (Nat, Nat) Position where
    cast (line, column) = MkPos line column

export
Cast Position (Nat, Nat) where
    cast (MkPos line column) = (line, column)

export
Show Position where
    show pos = fastConcat [show pos.line, ":", show pos.column]

||| A label for part of parsing: either a token or a name.
public export
data Label : (tok : Type) -> Type where
    Token : tok -> Label tok
    Named : String -> Label tok

prettyLabel : Show tok => Label tok -> String
prettyLabel (Token tok) = show tok
prettyLabel (Named name) = name

||| An error occuring during parsing.
public export
data RawParseError : (tok : Type) -> Type where
    ||| Unexpected token or EOF, along with expected tokens.
    ||| @ t the token or EOF found; `Just _` represents a token, `Nothing`
    |||     represents EOF.
    ||| @ ts the expected parts of parsing.
    Unexpected :
        (t : Maybe tok) ->
        (ts : List $ Label tok) ->
        RawParseError tok

||| Create an `Unexpected` error with a single expected token.
export total
unexpected1 : Maybe tok -> Label tok -> RawParseError tok
unexpected1 t = Unexpected t . pure

export
Semigroup (RawParseError tok) where
    Unexpected t s1 <+> Unexpected _ s2 = Unexpected t (s1 <+> s2)

prettyRawParseError : Show tok => RawParseError tok -> String
prettyRawParseError (Unexpected t lbls) =
    let prettyT = case t of
            Just t' => "token " <+> show t'
            Nothing => "end of file"
        prettyLbls = case lbls of
            [] => []
            (lbl :: lbls') => "; expected " :: prettyLabel lbl :: map (\lbl' => ", " <+> prettyLabel lbl') lbls'
    in fastConcat $
        "unexpected "
            :: prettyT
            :: prettyLbls

||| A parse error equipped with position information.
public export
record ParseError tok where
    constructor MkParseError
    pos : Position
    rawError : RawParseError tok

||| Pretty-print a parse error.
export
prettyParseError : Show tok => ParseError tok -> String
prettyParseError err = fastConcat
    [ "parse error at "
    , show err.pos
    , "\n"
    , prettyRawParseError err.rawError
    ]

||| A parser which returns a value of type `a`
public export
record Parser tok a where
    constructor MkParser
    result : Position -> Either (RawParseError tok) a
    next : Position -> tok -> Either (RawParseError tok) (Parser tok a)

public export covering
Functor (Parser tok) where
    map f p = MkParser
        { result = \pos => f <$> p.result pos
        , next = \pos, t => map f <$> p.next pos t
        }

covering
alt : Parser tok a -> Parser tok a -> Parser tok a
alt p1 p2 = MkParser
    { result = \pos => case (p1.result pos, p2.result pos) of
        (Left e1, Left e2) => Left (e1 <+> e2)
        (Right x, _) => Right x
        (_, Right x) => Right x
    , next = \pos, t => case (p1.next pos t, p2.next pos t) of
        (Left e1, Left e2) => Left (e1 <+> e2)
        (Right p1', Left _) => Right p1'
        (Left _, Right p2') => Right p2'
        (Right p1', Right p2') => Right $ alt p1' p2'
    }

public export covering
Applicative (Parser tok) where
    pure x = MkParser
        { result = \_ => Right x
        , next = \_, tok => Left $ Unexpected (Just tok) neutral
        }
    pf <*> px = MkParser
        { result = \pos => pf.result pos <*> px.result pos
        , next = \pos, t =>
            let pfx = (<*> px) <$> pf.next pos t
            in case pf.result pos of
                Left e => mapFst (e <+>) pfx
                Right f => case (pfx, px.next pos t) of
                    (Left e1, Left e2) => Left (e1 <+> e2)
                    (Right pfx', Left _) => Right pfx'
                    (Left _, Right px') => Right $ map f px'
                    (Right pfx', Right px') => Right $ pfx' `alt` map f px' 
        }

public export covering
Alternative (Parser tok) where
    empty = MkParser
        { result = \_ => Left $ Unexpected Nothing neutral
        , next = \_, tok => Left $ Unexpected (Just tok) neutral
        }
    (<|>) = alt

public export covering
Monad (Parser tok) where
    px >>= f = MkParser
        { result = \pos =>
            case px.result pos of
                Left e => Left e
                Right x => case (f x).result pos of
                    Left e => Left e
                    Right fx => Right fx
        , next = \pos, t =>
            let pxf = (>>= f) <$> px.next pos t
            in case px.result pos of
                Left e => mapFst (e <+>) pxf
                Right x => case (pxf, (f x).next pos t) of
                    (Left e1, Left e2) => Left (e1 <+> e2)
                    (Right pxf', Left _) => Right pxf'
                    (Left _, Right pfx) => Right pfx
                    (Right pxf', Right pfx) => Right $ pxf' <|> pfx
        }

||| Proof that an `Either` is `Left`.
public export
data IsLeft : Either a b -> Type where
    ItIsLeft : IsLeft (Left a)

||| Proof that a parser cannot accept an empty input.
public export
data NonEmpty : Parser tok a -> Type where
    IsNonEmpty : ((pos : Position) -> IsLeft (p.result pos)) -> NonEmpty p
