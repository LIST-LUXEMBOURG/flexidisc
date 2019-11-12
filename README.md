# Flexidisc

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT)

Typesafe extensible records (and more) for Idris.

## About

This library proposed an implementation of extensible records in Idris.
Extensible records provide a way to consider labels as first class objects
in a record.
It allows the developper to add, remove and change types of a field in a
record.

Aside these core capabilities, `Flexidisc` also provides more advanced extensible
manipulation function to modify, validate extensible records and to handle
heterogeneous list of records.

## Getting started

### Prerequisites

As `flexidisc` is an [Idris](https://www.idris-lang.org) library, your supposed to have
a working version of `idris` on your computer.
`flexidisc` was teste on `idris` 1.3.2, but should work on prior version of `idris`.

`flexidisc` has no other external dependencies.

### Installation

```
$ git clone https://git.list.lu/nbiri/flexidisc.git
$ cd flexidisc
$ idris --install flexidisc.ipkg
> :module Flexidisc
```

To include the library in idris, you can either specify it when you run the REPL:

```
$ idris -p flexidisc
```

Or add the dependency to your project `ipkg` file.

If you want, you can also load the `Tutorial` file to use it as a start
(you can also take a look now at the [tutorial file] to see example of
record manipulations):

```
$ idris -p flexidisc examples/Tutorial.idr
```

There's no `nix` install at this stage, I should work on it.

## Features

- Record extension
- Projection
- Typesafe accesses/updates
- Concatenation of disjoint records
- Pach a record with another one
- Order independent equality of records
- Row polymorphic functions
- List of heterogeneous records + operations on them

## Usage

The core of `Flexidisc` is the `Record` type:

```
Record : (key : Type) -> (header : Header key) -> Type
```

`Record` takes two parameter:

- `key`, the type used to identify the different rows of a `Record`.
  A `key` must implement `DecEq` interface (to avoid duplicate fields),
  and `Ord` (to allow field declaration in any order).
- `header` can be seen as a list of `(key, Type)` pairs, that identify
  the type of each row in the Record.

### Record creation

```
johnDoe : Record String ["Firstname" ::: String, "Age" ::: Nat])
johnDoe = ["Firstname" := "John", "Age" := 42]
```

### Record extension

```
agedJohn : Record String ["Age" ::: Nat, "Lastname" ::: String, "Firstname" ::: String]
agedJohn = ("Lastname" := "Doe") :: johnDoe
```

We can also append disjoints records with `++`:

```
idJohn : Record String ["ID" ::: Nat, "Firstname" ::: String, "Lastname" ::: String, "Age" ::: Nat]
idJohn = ["ID" := the Nat 1, "Firstname" := "John"] ++ ["Lastname" := "Doe", "Age" := the Nat 42]
```

### Record projection

```
johnsName : Record ["Lastname" ::: String, "Firstname" ::: String]
johnsName = project agedJohn
```

```
keepJohn : Record ["Firstname" ::: String]
keepJohn = keep "Firstname" ageLast
```

```
backToJohnDoe : Record ["Firstname" ::= String, "LastName" ::= String]
backToJohnDoe = drop "Age" agedJohn
```

```
john : Record ["Firstname" ::= String]
john = discard ["Lastname", "Age"] agedJohn
```

### Going further

The [examples] contains several usage examples of more advanced use of the library.


## Type-Safety

Manipulation functions provided in the library are type safe.

Type safety is mostly handled by idris [automatic proof generation].

Here are a few examples of type checking failure
(more precisely, failure by not succeeding to generate a proof):

```
get "Age" johnDoe
-- Can't prove that "Age" is a row of johnDoe

("Firstname" := "Nicolas") :: johnDoe
-- Can't create a duplicate label

the (Record ["Firstname" ::: String, "Age" ::: Nat]) (project johnDoe)
-- Can't create labels during a projecttion

john ++ johnDoe
-- Can't merge two records with a common field
```

## Limitations

### Type inference

The result type of some functions such as `keep` or `patch` cant be inferred
from the function parameters.
The reason is that the result type is not given by a function but by a proof
construction, and not computed.

Of course, the same goes with functions like `project` or `reorder`, for which
there are many possibilities ofr the result type.


[tutorial file]: tree/master/examples/Tutorial.idr
[examples]: tree/master/examples
[automatic proof generation]: http://docs.idris-lang.org/en/latest/tutorial/miscellany.html#auto-implicit-arguments
