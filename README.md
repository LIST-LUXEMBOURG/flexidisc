# CleanRecord

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT)

## Overview

`CleanRecord` is an typesafe implementation of extensible records in Idris.
An extensible record is a record that can be extended or shrink on demand.

### Features

- Inferred (from type) or explicit labels
- Record extension
- Projection
- Typesafe accesses/updates
- Concatenation of disjoint records
- Pach a record with another one
- Order dependent equality of records
- Order independent equality of records
- Row polymorphic operations

## Getting started

Idris sohuld be available on your computer.
Then, the easiest way to start with CleanRecord is to clone this repository:

Clone this repository, go into its dirctory, and install the `clean_record`
package.

Install it:

```
$ cd cleanRecord
$ idris --install clean_record.ipkg
```

And then start idris REPL with the `clean_record` package:

```
$ idris -p clean_record
Idris> :module CleanRecord
```

If you want, you can also load the `Tutorial` file to use it as a start
(you can also take a look now at the [tutorial file] to see example of
record manipulations):

```
$ idris -p clean_record examples/Tutorial.idr
```

## Usage

### Record creation

Two functions can be used to create `Record`s, `rec` and `namedRec`.

`rec` relies on the type signature to associate provided values to a field.
For example, if you want to create a `Person` with a `Firstname` and an
`Age`, you can write:

```
johnDoe : Record ["Firstname" := String, "Age" :=  Nat])
johnDoe = rec ["John", 42]
```

Depending on the scenarios, it may be easier to declare the row names
along with the data.
It's the purpose of `namedRec`. To build the same record, this time, the syntax is:

```
namedJohnDoe : Record ["Firstname" := String, "Age" :=  Nat])
namedJohnDoe = namedRec ["Firstname" ::= "John", "Age" ::=  the Nat 42]
```

You don't see any difference there but in this last case,
the type would have been infered, while it wouldn't in the first case.

### Record extension

Suppose that we want to add a lastname to the previous example,
we can suse the usual `::` operator:

```
agedJohn : Record ["Age" := Nat, "Lastname" := String, "Firstname" := String]
agedJohn =  42 :: namedJohnDoe
```

And again, there's an equivalent for named field:

```
namedAgedJohn : Record ["Age" := Nat, "Lastname" := String, "Firstname" := String]
namedAgedJohn = ("Age" ::= the Nat 42) :+: namedJohn
```

We can also append disjoints records with `++`:

```
idJohn : Record [("ID", Nat), ("Firstname", String), ("Lastname", String), ("Age", Nat)]
idJohn = namedRec ["ID" ::= the Nat 1, "Firstname" ::= "John"]
      ++ namedRec ["Lastname" ::= "Doe", "Age" ::= the Nat 42]
```

## Record projection and reordering

We can also easily delete rows or reorder them.
As in many libraries support of extensible records,
the rows order is significant in `CleanRecord`.
Although, in many situations, we don't want to consider
this order.
A workaround is to provide a way to easily reorder a record:

```
ageLast : Record [("Lastname", String), ("Firstname", String), ("Age", Nat)]
ageLast = reorder agedJohn
```

`reorder` ensures that all the rows are still in the record after the
preservation.
You can, however, decide to use a more permisive functions, `project`,
if you want to skip som of the rows of the original record:

```
john : Record ["Firstname" ::= String]
john = project ageLast
```

or the named alternative:

```
keepJohn : Record ["Firstname" ::= String]
keepJohn = keep "Firstname" ageLast
```

You can also decide to drop a specific row:

```
backToJohnDoe : Record ["Firstname" ::= String, "LastName" ::= String]
backToJohnDoe = dropByName "Age" agedJohn
```

or specific row**s**:

```
john : Record ["Firstname" ::= String]
john = dropN ["Lastname", "Age"] agedJohn
```

# Type-Safety

The CleanRecord manipulation functions provided in the library are type safe.

Type safety is mostly handled by idris [automatic proof generation].

Here are a few examples of type checking failure
(more precisely, failure by not succeeding to generate a proof):

```
 -- Can't prove that "Age" is a row of johnDoe
get "Age" johnDoe

-- Can't create a duplicate label
("Firstname" ::= "Nicolas") :+: johnDoe

-- Can't create labels during a projecttion
the (Record ["Firstname" := String, "Age" := Nat]) (project johnDoe)

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
