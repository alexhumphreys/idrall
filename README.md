# Idrall

[Dhall](https://dhall-lang.org) bindings for [Idris](https://www.idris-lang.org).

Parse, evaluate, check/infer types of Dhall expressions.

## Status￼

Very much a work in progress, with many thing missing. The plan is to make an end to end compiler for a small goofy subset of Dhall, and gradually and features.￼

## Missing features

- [x] Fuctions
- [x] Types
  - [x] Bool
  - [x] Natural
  - [x] List
  - [x] Equivalent
  - [] String
  - [] Integer
  - [] Optional
  - [] Records
- Operators
  - [x] `&&`
  - [x] `#`
  - [] `\\`
  - [] `/\`
  - [] `::`
  - etc.
- Builtins
  - [] `Natural/IsZero`
  - [] Everything else
- Imports
  - [x] local files
  - [] Env
  - [] http
- [] `x@1` style variables
- Anything to do with caching
- CBOR representation
- The rest of this list

Right now you can basically just do you type annotations, create naturals/lists/bools, assigned them with let, and create functions.

## Dependencies

[Lightyear](https://github.com/ziman/lightyear)

## Installation

Not sure, need to add some `.ipkg` file I think...

## Tests

So far there's only the type inference tests, you can run them from the repl like so:

```
idris -p lightyear tests/Test.idr
*tests/Test> :exec testAll
```

They mostly fail, so you can run the ones that should pass with the following:

```
*tests/Test> :exec testGood
```

## Implementation details￼

### Type checking

Type checking and inference (aka synthesis) in Dhall is covered by [these rules](https://github.com/dhall-lang/dhall-lang/blob/master/standard/type-inference.md). The rules are implemented here using a technique called Normalisation by Evaluation (NbE). It is described in [this paper by David Christiansen](http://davidchristiansen.dk/tutorials/implementing-types-hs.pdf), and was also used by [@AndrasKovaks](https://github.com/AndrasKovacs) in [their branch](https://github.com/dhall-lang/dhall-haskell/commits/nbe-elaboration) on `dhall-Haskell` (I found [this commit](https://github.com/dhall-lang/dhall-haskell/commit/627a6cdea0170336ff08de34851d8bdf5180571d) particularly useful).

The general idea of NbE is that you have a data structure that represents￼ the raw syntax￼￼ Language￼, which is called `Expr` here. Expressions can be literals (`3`, `True`), types (`Natural`, `Bool`, `Type`), functions, builtins, operators, etc. You evaluate the `Expr` to a data structure that only represents expressions that cannot be reduced further￼, called `Value` here. Eg, the expression `True && False` can be represented in an `Expr`, but as a `Value` would be reduced to `False`. 

To convert a `Value` back to an `Expr` is called "reading back" or "quoting".

To normalise an `Expr` you evaluate it to a `Value`, then read it back to a `Expr`, this which ensures it's fully normalised.

Type synthesis (or type inference) takes an `Expr` and returns its type as a `Value`. 

Type checking checks an `Expr` against a type given as a `Value`. A `Value` is synthesised for the type of the `Expr`, and both this `Value` and the provided type `Value` are read back to `Expr`s. This ensures there are no reducible expressions in either. Now you can compare the types using an alpha equivalence check to see if they match.

That was a very brief, potentially wrong introduction to the NbE technique used. I'm glossing over a bunch of details about closures, neutral values, the environment/context, etc. but this should be enough to get started with. See the above paper for a full description, and check out the code to see it in action.￼

## Contributions

Any contributions would be appreciated, and anything from the missing list above would be a good place to start￼.

### Examples of adding language features

Adding features generally means editing the `Expr` and `Value` types, the parser, the `eval`/`check`/`synth` functions, the tests etc.

As an example, the `List` type was added via [#1](https://github.com/alexhumphreys/idrall/pull/1), and literal values of type list (`[1, 2, 3]`) were added via [#2](https://github.com/alexhumphreys/idrall/pull/2). For an example of an operator, [#3](https://github.com/alexhumphreys/idrall/pull/3) adds the `#` operator for appending lists.

## Future work

- Add the things from the missing list above
- ￼Upgrade to Idris2￼ (need to see what's up with Lightyear for this)
- Improved parsing (Not really sure what I'm doing here)￼
- Think about what api/types to expose so as to make this as nice as possible to use
