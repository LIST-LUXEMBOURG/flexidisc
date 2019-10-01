module Flexidisc.Record.Type

import        Flexidisc.RecordContent
import public Flexidisc.THList

import public Flexidisc.OrdHeader
import public Flexidisc.Dec.IsYes
import public Flexidisc.Header
import public Flexidisc.TaggedValue

%default total
%access export

-- CREATE

||| A `Record` is a set of rows
||| @ k      The type of the labels
||| @ header The list of rows into the record, with their types
public export
data RecordM : (m : Type -> Type) -> (k : Type) -> (header : Header k) -> Type where
  Rec : (o : Ord k) =>
        (values : RecordContentM m k o header) -> (nubProof : Nub header) ->
        RecordM m k (H header)

public export
Record : (k : Type) -> (header : Header k) -> Type
Record = RecordM id

infix 6 :::

||| Convenient helper for row type readability
public export
(:::) : (k : l) -> (v : Type) -> Pair l Type
(:::) = MkPair

%name Record xs, ys, zs

||| The empty record
public export
Nil : Ord k => RecordM m k []
Nil = Rec empty []

||| Insert a new row in a record (with explicit proof)
public export
cons' : (DecEq k, Ord k) => TaggedValue k' (m ty) -> RecordM m k header ->
        (fresh : Fresh k' header) ->
        RecordM m k ((k', ty) :: header)
cons' x (Rec xs isnub) (F fresh) =
  Rec (insert x xs) (freshInsert fresh isnub)

||| Insert a new row in a record
public export
cons : (DecEq k, Ord k) => TaggedValue k' (m ty) -> RecordM m k header ->
       {default SoTrue fresh : IsFresh k' header} ->
       RecordM m k ((k', ty) :: header)
cons x xs {fresh} = cons' x xs (getProof fresh)

||| Insert a new row in a record
public export
(::) : (DecEq k, Ord k) => TaggedValue k' (m ty) -> RecordM m k header ->
       {default SoTrue fresh : IsFresh k' header} ->
       RecordM m k ((k', ty) :: header)
(::) = cons

||| It's just monomorphic `id` with a fancy name, to help type inference
recM : (m : Type -> Type) -> RecordM m k header -> RecordM m k header
recM _ = id

||| It's just monomorphic `id` with a fancy name, to help type inference
rec : Record k header -> Record k header
rec = id

namespace test
  %access private

  test_rec1 : Record String ["Firstname" ::: String]
  test_rec1 = ["Firstname" := "John"]

  test_rec2 : Record String ["Lastname" ::: String, "Firstname" ::: String]
  test_rec2 = ["Firstname" := "John", "Lastname" := "Doe"]

