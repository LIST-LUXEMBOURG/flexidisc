module CleanRecord.Record

import        CleanRecord.RecordContent

import public CleanRecord.Dec.IsYes
import public CleanRecord.Header
import public CleanRecord.OrdHeader
import public CleanRecord.Record.Type
import public CleanRecord.Record.Read
import public CleanRecord.Record.Update
import public CleanRecord.TaggedValue
import public CleanRecord.THList

%default total
%access export


||| Append two records, it fails if some fields are duplicated
|||
||| Complexity is _O(n)_ where _n_ is the length of the longest record.
|||
merge : (xs : Record k header) -> (ys : Record k header') ->
        {auto prf : Disjoint header header'} ->
        Record k (merge header header')
merge (Rec xs nubX) (Rec ys nubY) {prf = D prf} =
  Rec (merge xs ys) (disjointNub prf nubX nubY)

||| Alias for `merge`
(++) : (xs : Record k header) -> (ys : Record k header') ->
       {auto prf : Disjoint header header'} ->
       Record k (merge header header')
(++) = merge


(|>) : DecEq k =>
       (xs : Record k header) -> (ys : Record k header') ->
       {default (S Same) prf : SameOrd header header'} ->
        Record k (patch header header')
(|>) (Rec xs nubX) (Rec ys nubY) {prf = S prf} = let
  nubProof = disjointNub diffIsDisjoint (isNubFromSub diffIsSub nubY) nubX
  in Rec (xs |> ys) nubProof

-- DELETE

||| Remove a row from a Record.
|||
||| Complexity is _O(n)_
|||
||| @ xs the record
||| @ loc  the proof that the row is in it
dropByLabel : (xs : Record k header) -> (loc : Label query header) ->
              Record k (dropLabel header loc)
dropByLabel (Rec xs nub) (L prf) =
  Rec (drop xs prf) (dropPreservesNub nub prf)

||| Remove a row from a Record.
|||
||| Complexity is _O(n)_
|||
||| @ query  the row name
||| @ xs     the record
||| @ loc    the proof that the row is in it
drop : (query : k) -> (xs : Record k header) ->
       {auto loc : Label query header} ->
       Record k (dropLabel header loc)
drop _ xs {loc} = dropByLabel xs loc

-- TRANSFORM

||| Project a record (keep only a subset of its field and reorder them.
|||
||| Complexity is _O(n)_
|||
project : Record k header -> {auto prf : Sub sub header} -> Record k sub
project (Rec xs nub) {prf = S prf} = Rec (project xs prf) (isNubFromSub prf nub)

||| Build a projection with the given keys
|||
||| @keys The rows to keep
||| @xs The record to project
||| @prf Proof that the rows are parts of the record
keep : (keys : List k) -> (xs : Record k pre) ->
       {auto prf : SubWithKeys keys post pre} ->
       Record k post
keep keys (Rec xs nub) {prf = S prf} =
  Rec (keep xs prf) (isNubFromSub (toSub prf) nub)

||| Build a projection that excludes the given keys
|||
||| @keys The rows to skip
||| @xs The record to project
||| @prf Proof that the rows are parts of the record
discard : (keys : List k) -> (xs : Record k pre) ->
          {auto prf : CompWithKeys keys post pre} ->
          Record k post
discard keys (Rec xs nub) {prf = S prf} =
  Rec (discard xs prf) (isNubFromSub (toSub prf) nub)

decLabel : DecEq k => (l : k) -> (xs : Record k header) -> Dec (Label l header)
decLabel l _ {header} = decLabel l header


toTHList : Record k header -> THList (toList header)
toTHList (Rec xs _) = toTHList xs


-- COMPARE

implementation
Eq (THList (toList header)) => Eq (Record k header) where
  (==) xs ys = toTHList xs == toTHList ys
  (/=) xs ys = toTHList xs /= toTHList ys
