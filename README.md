# CleanRecord

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT)

`CleanRecord` is an typesafe implementation of extensible records in Idris.
An extensible record is a record that can be extended or shrink on demand.

## Getting started

Idris sohuld be available on your computer.
Then, the easiest way to start with CleanRecord is to clone this repository:

```
$ git clone https://git.list.lu/nbiri/cleanRecord.git

```

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

If you want, you can also load the Tutorial file to use it as a start:

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
*CleanRecord> the (Record ["Firstname" := String, "Age" :=  Nat]) $ rec ["John", 42]
MkRecord ["John", 42] (SoFalse :: SoFalse :: []) : Record [("Firstname", String), ("Age", Nat)]
```

Depending on the scenarios, it may be easier to declare the row names
along with the data.
It's the purpose of `namedRec`. To build the same record, this time, the syntax is:

```
*CleanRecord> namedRec ["Firstname" ::= "John", "Age" ::=  the Nat 42]
MkRecord ["John", 42] (SoFalse :: SoFalse :: []) : Record [("Firstname", String), ("Age", Nat)]
```

### Record extension

Suppose that we want to add a lastname to the previous example,
we can suse the usual `::` operator:

```
*CleanRecord> namedRec ["Firstname" ::= "John", "Age" ::=  the Nat 42]
MkRecord ["John", 42] (SoFalse :: SoFalse :: []) : Record [("Firstname", String), ("Age", Nat)]
*CleanRecord> the (Record ["Lastname" := String, "Firstname" := String, "Age" := Nat]) $ "Doe" :: it
MkRecord ["Doe", "John", 42] (SoFalse :: SoFalse :: SoFalse :: []) : Record [("Lastname", String),
                                                                             ("Firstname", String),
                                                                             ("Age", Nat)]
```

And again, there's an equivalent for named field:

```
*CleanRecord> namedRec ["Firstname" ::= "John", "Age" ::= the Nat 42]
MkRecord ["John", 42] (SoFalse :: SoFalse :: []) : Record [("Firstname", String), ("Age", Nat)]
*CleanRecord> "Lastname" ::= "Doe" :+: it
MkRecord ["Doe", "John", 42] (SoFalse :: SoFalse :: SoFalse :: []) : Record [("Lastname", String),
                                                                             ("Firstname", String),
                                                                             ("Age", Nat)]
```

We can also append disjoints records with `++`:

```
*CleanRecord> namedRec ["ID" ::= the Nat 1, "Firstname" ::= "John"] ++ namedRec ["Lastname" ::= "Doe", "Age" ::= the Nat 42]
MkRecord [1, "John", "Doe", 42] (SoFalse :: SoFalse :: SoFalse :: SoFalse :: []) : Record [("ID", Nat),
                                                                                           ("Firstname", String),
                                                                                           ("Lastname", String),
                                                                                           ("Age", Nat)]
```