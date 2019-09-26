# Flexidisc

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT)



`Flexidisc` is an typesafe implementation of extensible records in Idris.
An extensible record is a record that can be extended, shrink or modified on demand.

### Why?

The initial motivation was to handle data transformation pipeline, where you want to
create, modify and delete fields from records while presesrving type safety.

### Features

- Record extension
- Projection
- Typesafe accesses/updates
- Concatenation of disjoint records
- Pach a record with another one
- Order independent equality of records
- Row polymorphic functions
- List of heterogeneous records + operations on them

## Getting started

Idris sohuld be available on your computer.
Then, the easiest way to start with Flexidisc is to clone this repository:

Clone this repository, go into its dirctory, and install the `clean_record`
package.

Install it:

```
$ cd flexidisc
$ idris --install flexidisc.ipkg
```

And then start idris REPL with the `flexidisc` package:

```
$ idris -p flexidisc
Idris> :module Flexidisc
```

If you want, you can also load the `Tutorial` file to use it as a start
(you can also take a look now at the [tutorial file] to see example of
record manipulations):

```
$ idris -p clean_record examples/Tutorial.idr
```

There's no `nix` install at this stage, I should work on it.

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

## Record projection

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

# Type-Safety

The Flexidisc manipulation functions provided in the library are type safe.

Type safety is mostly handled by idris [automatic proof generation].

Here are a few examples of type checking failure
(more precisely, failure by not succeeding to generate a proof):

```
 -- Can't prove that "Age" is a row of johnDoe
get "Age" johnDoe

-- Can't create a duplicate label
("Firstname" := "Nicolas") :: johnDoe

-- Can't create labels during a projecttion
the (Record ["Firstname" ::: String, "Age" ::: Nat]) (project johnDoe)

-- Can't merge two records with a common field
john ++ johnDoe
```

# Limitations

## Type inference

The result type of some functions such as `keep` or `patch` cant be inferred
from the function parameters.
The reason is that the result type is not given by a function but by a proof
construction, and not computed.

Of course, the same goes with functions like `project` or `reorder`, for which
there are many possibilities ofr the result type.


[tutorial file]: blob/master/examples/Tutorial.idr
[automatic proof generation]: http://docs.idris-lang.org/en/latest/tutorial/miscellany.html#auto-implicit-arguments
