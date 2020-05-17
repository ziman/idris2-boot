module Text.Parser.Core

import public Control.Delayed
import Data.List

data CommitScope = Uncommitted | Scoped | Absolute

Semigroup CommitScope where
  Uncommitted <+> cs = cs
  cs <+> Uncommitted = cs
  Absolute <+> cs = Absolute
  cs <+> Absolute = Absolute
  Scoped <+> Scoped = Scoped

Monoid CommitScope where
  neutral = Uncommitted

||| Description of a language's grammar. The `tok` parameter is the type
||| of tokens, and the `consumes` flag is True if the language is guaranteed
||| to be non-empty - that is, successfully parsing the language is guaranteed
||| to consume some input.
public export
data Grammar : (tok : Type) -> (consumes : Bool) -> Type -> Type where
     Empty : (val : ty) -> Grammar tok False ty
     Terminal : String -> (tok -> Maybe a) -> Grammar tok True a
     NextIs : String -> (tok -> Bool) -> Grammar tok False tok
     EOF : Grammar tok False ()

     Fail : String -> Grammar tok c ty
     Commit : (cs : CommitScope) -> Grammar tok False ()
     WithCommitScope : Grammar tok c a -> Grammar tok c a

     SeqEat : {c2 : _} -> Grammar tok True a -> Inf (a -> Grammar tok c2 b) ->
              Grammar tok True b
     SeqEmpty : {c1, c2 : _} -> Grammar tok c1 a -> (a -> Grammar tok c2 b) ->
                Grammar tok (c1 || c2) b
     Alt : {c1, c2 : _} -> Grammar tok c1 ty -> Grammar tok c2 ty ->
           Grammar tok (c1 && c2) ty

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume some input. If the first one consumes input, the
||| second is allowed to be recursive (because it means some input has been
||| consumed and therefore the input is smaller)
public export %inline
(>>=) : {c1, c2 : Bool} ->
        Grammar tok c1 a ->
        inf c1 (a -> Grammar tok c2 b) ->
        Grammar tok (c1 || c2) b
(>>=) {c1 = False} = SeqEmpty
(>>=) {c1 = True} = SeqEat

||| Sequence two grammars. If either consumes some input, the sequence is
||| guaranteed to consume input. This is an explicitly non-infinite version
||| of `>>=`.
export
seq : {c1, c2 : _} -> Grammar tok c1 a ->
      (a -> Grammar tok c2 b) ->
      Grammar tok (c1 || c2) b
seq = SeqEmpty

||| Sequence a grammar followed by the grammar it returns.
export
join : {c1, c2 : Bool} ->
       Grammar tok c1 (Grammar tok c2 a) ->
       Grammar tok (c1 || c2) a
join {c1 = False} p = SeqEmpty p id
join {c1 = True} p = SeqEat p id

||| Give two alternative grammars. If both consume, the combination is
||| guaranteed to consume.
export
(<|>) : {c1, c2 : _} ->
        Grammar tok c1 ty ->
        Grammar tok c2 ty ->
        Grammar tok (c1 && c2) ty
(<|>) = Alt

||| Allows the result of a grammar to be mapped to a different value.
export
{c : _} -> Functor (Grammar tok c) where
  map f (Empty val)  = Empty (f val)
  map f (Fail msg) = Fail msg
  map f (Terminal msg g) = Terminal msg (\t => map f (g t))
  map f (Alt x y)    = Alt (map f x) (map f y)
  map f (WithCommitScope rhs) = WithCommitScope $ map f rhs
  map f (SeqEat act next)
      = SeqEat act (\val => map f (next val))
  map f (SeqEmpty act next)
      = SeqEmpty act (\val => map f (next val))
  -- The remaining constructors (NextIs, EOF, Commit) have a fixed type,
  -- so a sequence must be used.
  map {c = False} f p = SeqEmpty p (Empty . f)

||| Sequence a grammar with value type `a -> b` and a grammar
||| with value type `a`. If both succeed, apply the function
||| from the first grammar to the value from the second grammar.
||| Guaranteed to consume if either grammar consumes.
export
(<*>) : {c1, c2 : _} ->
        Grammar tok c1 (a -> b) ->
        Inf (Grammar tok c2 a) ->
        Grammar tok (c1 || c2) b
(<*>) {c1 = False} x y = SeqEmpty x (\f => map f y)
(<*>) {c1 = True } x y = SeqEmpty x (\f => map f (Force y))

||| Sequence two grammars. If both succeed, use the value of the first one.
||| Guaranteed to consume if either grammar consumes.
export
(<*) : {c1, c2 : _} ->
       Grammar tok c1 a ->
       Inf (Grammar tok c2 b) ->
       Grammar tok (c1 || c2) a
(<*) x y = map const x <*> y

||| Sequence two grammars. If both succeed, use the value of the second one.
||| Guaranteed to consume if either grammar consumes.
export
(*>) : {c1, c2 : _} ->
       Grammar tok c1 a ->
       Inf (Grammar tok c2 b) ->
       Grammar tok (c1 || c2) b
(*>) x y = map (const id) x <*> y

||| Produce a grammar that can parse a different type of token by providing a
||| function converting the new token type into the original one.
export
mapToken : (a -> b) -> Grammar b c ty -> Grammar a c ty
mapToken f (Empty val) = Empty val
mapToken f (Terminal msg g) = Terminal msg (g . f)
mapToken f (NextIs msg g) = SeqEmpty (NextIs msg (g . f)) (Empty . f)
mapToken f EOF = EOF
mapToken f (Fail msg) = Fail msg
mapToken f (Commit cs) = Commit cs
mapToken f (WithCommitScope rhs) = WithCommitScope $ mapToken f rhs
mapToken f (SeqEat act next) = SeqEat (mapToken f act) (\x => mapToken f (next x))
mapToken f (SeqEmpty act next) = SeqEmpty (mapToken f act) (\x => mapToken f (next x))
mapToken f (Alt x y) = Alt (mapToken f x) (mapToken f y)

||| Always succeed with the given value.
export
pure : (val : ty) -> Grammar tok False ty
pure = Empty

||| Check whether the next token satisfies a predicate
export
nextIs : String -> (tok -> Bool) -> Grammar tok False tok
nextIs = NextIs

||| Look at the next token in the input
export
peek : Grammar tok False tok
peek = nextIs "Unrecognised token" (const True)

||| Succeeds if running the predicate on the next token returns Just x,
||| returning x. Otherwise fails.
export
terminal : String -> (tok -> Maybe a) -> Grammar tok True a
terminal = Terminal

export
withCommitScope : Grammar tok c a -> Grammar tok c a
withCommitScope = WithCommitScope

export
commitScoped : Grammar tok False ()
commitScoped = Commit Scoped

export
commitAbsolute : Grammar tok False ()
commitAbsolute = Commit Absolute

||| Always fail with a message
export
fail : String -> Grammar tok c ty
fail = Fail

||| Succeed if the input is empty
export
eof : Grammar tok False ()
eof = EOF

||| If the parser fails, treat it as a fatal error
export
mustWork : {c : Bool} -> Grammar tok c ty -> Grammar tok c ty
mustWork p = commitAbsolute *> p

data ParseResult : List tok -> (consumes : Bool) -> Type -> Type where
     Failure : {xs : List tok} ->
               (cs : CommitScope) ->
               (err : String) -> (rest : List tok) -> ParseResult xs c ty
     EmptyRes : (val : ty) -> (more : List tok) -> ParseResult more False ty
     NonEmptyRes : {xs : List tok} ->
                   (val : ty) -> (more : List tok) ->
                   ParseResult (x :: xs ++ more) c ty

-- Weaken the 'consumes' flag to take both alternatives into account
weakenRes : {whatever, c : Bool} -> {xs : List tok} ->
						ParseResult xs c ty -> ParseResult xs (whatever && c) ty
weakenRes (Failure cs msg ts) = Failure cs msg ts
weakenRes {whatever=True} (EmptyRes val xs) = EmptyRes val xs
weakenRes {whatever=False} (EmptyRes val xs) = EmptyRes val xs
weakenRes (NonEmptyRes {xs} val more) = NonEmptyRes {xs} val more

doParse : (act : Grammar tok c ty) ->
          (xs : List tok) -> 
          ParseResult xs c ty
-- doParse xs act with (sizeAccessible xs)
doParse (Empty val) xs = EmptyRes val xs
doParse (Fail str) [] = Failure neutral str []
doParse (Fail str) (x :: xs) = Failure neutral str (x :: xs)
doParse (Commit _) xs = EmptyRes () xs  -- commit has no effect unless on the LHS of Seq
doParse (Terminal err f) [] = Failure neutral "End of input" []
doParse (Terminal err f) (x :: xs)
      = maybe
           (Failure neutral err (x :: xs))
           (\a => NonEmptyRes {xs=[]} a xs)
           (f x)
doParse EOF [] = EmptyRes () []
doParse EOF (x :: xs)
      = Failure neutral "Expected end of input" (x :: xs)
doParse (NextIs err f) [] = Failure neutral "End of input" []
doParse (NextIs err f) (x :: xs)
      = if f x
           then EmptyRes x (x :: xs)
           else Failure neutral err (x :: xs)

doParse (WithCommitScope rhs) xs =
  case doParse rhs xs of
    Failure Scoped msg ts => Failure Uncommitted msg ts
    result => result

doParse (Alt {c1} {c2} x y) xs =
  case doParse x xs of
    Failure Uncommitted msg ts =>
      weakenRes {whatever = c1} (doParse y xs)
    Failure cs msg ts => Failure cs msg ts
    EmptyRes val xs => EmptyRes val xs
    NonEmptyRes {xs=xs'} val more => NonEmptyRes {xs=xs'} val more

-- strengthen failures coming from rhs
doParse (SeqEmpty {c1 = False} {c2} (Commit cs) rhs) xs =
  case doParse (rhs ()) xs of
    Failure cs' msg ts => Failure (cs <+> cs') msg ts
    result => result

doParse (SeqEmpty {c1} {c2} act next) xs
    = let p' = assert_total (doParse {c = c1} act xs) in
              case p' of
               Failure cs msg ts => Failure cs msg ts
               EmptyRes val xs =>
                     case assert_total (doParse (next val) xs) of
                          Failure cs' msg ts => Failure cs' msg ts
                          EmptyRes val xs => EmptyRes val xs
                          NonEmptyRes {xs=xs'} val more => 
                                           NonEmptyRes {xs=xs'} val more
               NonEmptyRes {x} {xs=ys} val more =>
                     case (assert_total (doParse (next val) more)) of
                          Failure cs' msg ts => Failure cs' msg ts
                          EmptyRes val _ => NonEmptyRes {xs=ys} val more
                          NonEmptyRes {x=x1} {xs=xs1} val more' =>
                               rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                                       NonEmptyRes {xs = ys ++ (x1 :: xs1)} val more'

doParse (SeqEat act next) xs with (doParse act xs)
  doParse (SeqEat act next) xs | Failure cs msg ts
       = Failure cs msg ts
  doParse (SeqEat act next) (x :: (ys ++ more)) | (NonEmptyRes {xs=ys} val more)
       = let p' = assert_total (doParse (next val) more) in
             case p' of
              Failure cs msg ts => Failure cs msg ts
              EmptyRes val _ => NonEmptyRes {xs=ys} val more
              NonEmptyRes {x=x1} {xs=xs1} val more' =>
                   rewrite appendAssociative (x :: ys) (x1 :: xs1) more' in
                           NonEmptyRes {xs = ys ++ (x1 :: xs1)} val more'
-- This next line is not strictly necessary, but it stops the coverage
-- checker taking a really long time and eating lots of memory...
-- doParse _ _ _ = Failure True True "Help the coverage checker!" []

public export
data ParseError tok = Error String (List tok)

||| Parse a list of tokens according to the given grammar. If successful,
||| returns a pair of the parse result and the unparsed tokens (the remaining
||| input).
export
parse : {c : _} -> (act : Grammar tok c ty) -> (xs : List tok) ->
        Either (ParseError tok) (ty, List tok)
parse act xs
    = case doParse act xs of
           Failure cs msg ts => Left (Error msg ts)
           EmptyRes val rest => pure (val, rest)
           NonEmptyRes val rest => pure (val, rest)
