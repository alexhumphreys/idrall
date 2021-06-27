# Idrall

![Ubuntu](https://github.com/alexhumphreys/idrall/workflows/Ubuntu/badge.svg)

[Dhall](https://dhall-lang.org) bindings for [Idris](https://www.idris-lang.org).

Parse, evaluate, check/infer types of Dhall expressions.

## Status

Still a work in progress, but for a given dhall expression with not much imports, idrall should be able to parse/type check and attempt evaluation. Type checker is pretty complete (one test is failing but that is due to [this Idris2 issue](https://github.com/idris-lang/Idris2/issues/29). Need to start running the other tests like parsing/normalisation etc. Everything around imports needs some work. There's now an elaborator reflection, but it's pretty new so will see how it handles.

## Derive Usage (WIP)

For an example of how to do a whole `parse -> resolve -> typecheck -> eval` pass of a dhall file, and marshall it into an idris type, check out the file [`./examples/Package.idr`](https://github.com/alexhumphreys/idrall/blob/master/examples/Package.idr)

There Is a `FromDhall` interface that you can use elaborator reflection to derive. You can use it for both ADTs and Records like so:

```
-- ADT example
data ExADT1
  = Foo
  | Bar Bool
  | Baz (Maybe Bool)

%runElab (deriveFromDhall ADT `{{ ExADT1 }})

-- Record example
record ExRec1 where
  constructor MkExRec1
  mn : Maybe Nat

%runElab (deriveFromDhall Record `{{ ExRec1 }})
```

There's implementations of `FromDhall` for `String`, `Nat`, `Integer`, `Bool`, `Double`, and `List`/`Maybe` of those. That interface gives you the `fromDhall` function you can use on dhall expression to get a `Maybe` of your Idris ADT or Record. See the `./tests/derive` dir for some examples.

The behaviour of this isn't thought out yet. For example, the `deriveFromDhall ADT` function ignores the dhall union and just looks for matching constructors. Also `deriveFromDhall Record` ignores extra fields on the dhall record. This behaviour may change. Also, as the elaborator reflection returns a `Maybe`, there's no good error messages when `fromDhall` fails, so that'll need updating.

## Indepth Usage (very alpha, YMMV)

Functions for parsing/evaluating/typechecking/resolving dhall expressions, should you need to ve a lot of control over how those things happen. These are all janky names and subject to change.

There's some functions in `Idrall/APIv1.idr` that expose the parsing/type checking/evaluation. The `valueFromString` function takes a dhall string, infers it's type, then evaluates it. If you have `idris2` installed you can run the following shell commands (prefixed with a `$`) from the root dir of this repo:

```
$ idris2 Idrall/APIv1.idr -p contrib --client ':exec doStuff valueFromString "{hello = 1, world = 2}.world + 3"'
Success: (VNaturalLit 5)
```

You can also create local dhall files, like the one provided at `examples/if-function.dhall`:

```
$ cat examples/if-function.dhall
let f = λ(x : Bool) →
  if x
  then "it's true!"
  else "nah"
in f True
```

and use `valueFromString` to evaluate them as follows. Note the path in the string:

```
$ idris2 Idrall/APIv1.idr -p contrib --client ':exec doStuff valueFromString "./examples/if-function.dhall"'
Success: (VTextLit (MkVChunks [] "it's true!"))
```

There's also a demo file at `Idrall/Demo.idr` which you can use to see a very rough example of how to read a Dhall file to and Idris type and use it natively. This is still very rough and verbose, but I hope to use [elaborator reflection](https://github.com/stefan-hoeck/idris2-elab-util) to improve this.

To see the types it is returning you'll want to check out [IOEither.idr](https://github.com/alexhumphreys/idrall/blob/master/Idrall/IOEither.idr) and [Value.idr](https://github.com/alexhumphreys/idrall/blob/master/Idrall/Value.idr).

There's still not much of an API, and this will hopefully change, but this should be enough to help you kick the tires if you're curious. If you find any problems or have any suggests, [issues](https://github.com/alexhumphreys/idrall/issues) and pull requests are welcome.

## Features

Most language features are in and should be working relatively correctly. The import system is incomplete, and other behaviour is also missing.

### Imports
- [x] Keyword: missing
- [x] Operator: ?
- [ ] Keyword: as Text
- [ ] Keyword: using
- [x] Local imports (/path/to/file.dhall)
- [ ] Environment variables
- [ ] HTTP imports
- [ ] Semantic integrity checks

### Other
- [ ] Normalisation under binders
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

Any contributions would be appreciated, also just try using this and opening any issues if you find any would be great. `grep`ing the code for `TODO` will show a lot of rough edges that could use some attention. If anything in the "Future work" section below catches your eye you can try that too!

### Examples of adding language features

Adding features generally means editing the `Expr` and `Value` types, the parser, the `eval`/`check`/`synth` functions, the tests etc.

As an example, the `List` type was added via [#1](https://github.com/alexhumphreys/idrall/pull/1), and literal values of type list (`[1, 2, 3]`) were added via [#2](https://github.com/alexhumphreys/idrall/pull/2). For an example of an operator, [#3](https://github.com/alexhumphreys/idrall/pull/3) adds the `#` operator for appending lists.

## Idris1 compatibility

There is an [`idris1` tag](https://github.com/alexhumphreys/idrall/releases/tag/idris1) which is the last confirmed commit that works with idris1. It's got all the dhall types and not much else, so if you're desperate for a Dhall implementation for idris1 it may help, but realistically you're gonna need the Idris2 version.

## Future work

- Add the missing things from the features list above.
- `Check.idr` takes about 8s to type check, should split up this file. Could be related to [this issue](https://github.com/idris-lang/Idris2/issues/797).
- Use dependent types to prove field names in values are elements of their Unions/Records.
- Improved parsing (Not really sure what I'm doing here)
- Think about what api/types to expose so as to make this as nice as possible to use.
- Try out [this reflection tutorial](https://github.com/stefan-hoeck/idris2-elab-util) to attempt to derive a generic `fromDhall` utility similar to the dhall-haskell implementation.
- Scope checking as found in [Tiny Idris](https://github.com/edwinb/SPLV20), you can find some failed attempts [here](https://github.com/alexhumphreys/idrall/blob/feat/scope-checking2/Idrall/Binder.idr).
