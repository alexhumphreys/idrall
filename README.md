# Idrall

[Dhall](https://dhall-lang.org) bindings for [Idris](https://www.idris-lang.org).

Parse, evaluate, check/infer types of Dhall expressions.

## Status

Still a work in progress with some things missing, but does have a lot of the language features. Check the list below to see how what is/isn't implemented.

## Features

Features marked with a tick should work for parsing, type checking and evaluation.

### Bool
- [x] Bool Type
- [x] Bool Literals
- [ ] Keyword: if/then/else
- [x] Operator: ||
- [x] Operator: &&
- [x] Operator: ==
- [x] Operator: !=

### Natural
- [x] Natural Type
- [x] Natural Literals
- [x] Operator: +
- [x] Operator: *
- [x] Function: Natural/even
- [x] Function: Natural/odd
- [x] Function: Natural/isZero
- [ ] Function: Natural/subtract
- [ ] Function: Natural/fold
- [ ] Function: Natural/build
- [ ] Function: Natural/show
- [x] Function: Natural/toInteger

### Integer
- [x] Integer Type
- [x] Integer Literals 
- [x] Function: Integer/negate
- [ ] Function: Integer/clamp
- [ ] Function: Integer/toDouble
- [ ] Function: Integer/show

### Double
- [x] Double Type
- [x] Double Literals
- [ ] Function: Double/show

### Text
- [x] Text Type
- [x] Text
- [ ] Function: Text/show
- [ ] Function: Text/replace
- [ ] Operator: ++

### List
- [x] List - Type
- [x] List
- [x] Operator: #
- [x] Function: List/fold
- [x] Function: List/build
- [x] Function: List/length
- [x] Function: List/head
- [x] Function: List/last
- [x] Function: List/indexed
- [x] Function: List/reverse

### Optional
- [x] Optional - Type
- [x] Optional
- [ ] Keyword: merge

### Records
- [x] Record types
- [x] Record values
- [x] Operator: ⩓
- [x] Operator: ∧
- [ ] Operator: ⫽
- [ ] Operator: ::
- [ ] Keyword: merge
- [ ] Keyword: toMap

### Imports
- [ ] Keyword: missing
- [ ] Operator: ?
- [ ] Keyword: as Text
- [ ] Keyword: using
- [x] Local imports (/path/to/file.dhall)
- [ ] Environment variables
- [ ] HTTP imports

### Other
- [x] Keyword: let
- [x] Keyword: assert
- [x] Pi types: Bool -> Bool
- [x] Functions: \(x : Bool) -> x
- [ ] `x@1` style variables
- [ ] Anything to do with caching
- [ ] CBOR representation

## Dependencies

[idris2](https://github.com/idris-lang/Idris2)

Not required, but some of the Makefile commands use [`rlwrap`](https://github.com/hanslub42/rlwrap) to make the Idris2 repl behave better.

## Installation

```
make install
```

## Tests

```
make test
```

## Implementation details

### Type checking

Type checking and inference (aka synthesis) in Dhall is covered by [these rules](https://github.com/dhall-lang/dhall-lang/blob/master/standard/type-inference.md). The rules are implemented here using a technique called Normalisation by Evaluation (NbE). It is described in [this paper by David Christiansen](http://davidchristiansen.dk/tutorials/implementing-types-hs.pdf), and was also used by [@AndrasKovaks](https://github.com/AndrasKovacs) in [their branch](https://github.com/dhall-lang/dhall-haskell/commits/nbe-elaboration) on `dhall-Haskell` (I found [this commit](https://github.com/dhall-lang/dhall-haskell/commit/627a6cdea0170336ff08de34851d8bdf5180571d) particularly useful).

The general idea of NbE is that you have a data structure that represents the raw syntax Language, which is called `Expr` here. Expressions can be literals (`3`, `True`), types (`Natural`, `Bool`, `Type`), functions, builtins, operators, etc. You evaluate the `Expr` to a data structure that only represents expressions that cannot be reduced further, called `Value` here. Eg, the expression `True && False` can be represented in an `Expr`, but as a `Value` would be reduced to `False`. 

To convert a `Value` back to an `Expr` is called "reading back" or "quoting".

To normalise an `Expr` you evaluate it to a `Value`, then read it back to a `Expr`, this which ensures it's fully normalised.

Type synthesis (or type inference) takes an `Expr` and returns its type as a `Value`. 

Type checking checks an `Expr` against a type given as a `Value`. A `Value` is synthesised for the type of the `Expr`, and both this `Value` and the provided type `Value` are read back to `Expr`s. This ensures there are no reducible expressions in either. Now you can compare the types using an alpha equivalence check to see if they match.

That was a very brief, potentially wrong introduction to the NbE technique used. I'm glossing over a bunch of details about closures, neutral values, the environment/context, etc. but this should be enough to get started with. See the above paper for a full description, and check out the code to see it in action.

## Contributions

Any contributions would be appreciated, and anything from the missing list above would be a good place to start.

### Examples of adding language features

Adding features generally means editing the `Expr` and `Value` types, the parser, the `eval`/`check`/`synth` functions, the tests etc.

As an example, the `List` type was added via [#1](https://github.com/alexhumphreys/idrall/pull/1), and literal values of type list (`[1, 2, 3]`) were added via [#2](https://github.com/alexhumphreys/idrall/pull/2). For an example of an operator, [#3](https://github.com/alexhumphreys/idrall/pull/3) adds the `#` operator for appending lists.

## Idris1 compatibility

There is an [`idris1` tag](https://github.com/alexhumphreys/idrall/releases/tag/idris1) which is the last confirmed commit that works with idris1. It's got all the dhall types and not much else, so if you're desperate for a Dhall implementation for idris1 it may help, but realistically you're gonna need the Idris2 version.

## Future work

- Add the things from the missing list above
- Use dependent types to prove field names in values are elements of their Unions/Records
- Improved parsing (Not really sure what I'm doing here)
- Think about what api/types to expose so as to make this as nice as possible to use
- Scope checking as found in [Tiny Idris](https://github.com/edwinb/SPLV20)
