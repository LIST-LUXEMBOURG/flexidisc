module Flexidisc.Record

import Control.Monad.Identity

import        Flexidisc.RecordContent

import public Flexidisc.Dec.IsYes
import public Flexidisc.Header
import public Flexidisc.Record.Type
import public Flexidisc.Record.Read
import public Flexidisc.Record.Update
import public Flexidisc.TaggedValue
import public Flexidisc.THList

%default total
%access export


||| Append two records, it fails if some fields are duplicated
|||
||| Complexity is _O(n)_ where _n_ is the length of the longest record.
|||
merge : (xs : RecordM m k header) -> (ys : RecordM m k header') ->
        {auto prf : Disjoint header header'} ->
        RecordM m k (merge header header')
merge (Rec xs nubX) (Rec ys nubY) {prf = D prf} =
  Rec (merge xs ys) (disjointNub prf nubX nubY)

||| Alias for `merge`
(++) : (xs : RecordM m k header) -> (ys : RecordM m k header') ->
       {auto prf : Disjoint header header'} ->
       RecordM m k (merge header header')
(++) = merge


||| Patch the right-hand side record with the values on the left-hand side
(|>) : DecEq k =>
       (xs : RecordM m k header) -> (ys : RecordM m k header') ->
       {default (S Same) prf : SameOrd header header'} ->
        RecordM m k (patch header header')
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
dropByLabel : (xs : RecordM m k header) -> (loc : Label query header) ->
              RecordM m k (dropLabel header loc)
dropByLabel (Rec xs nub) (L prf) =
  Rec (drop xs prf) (dropPreservesNub nub prf)

||| Remove a row from a Record.
|||
||| Complexity is _O(n)_
|||
||| @ query  the row name
||| @ xs     the record
||| @ loc    the proof that the row is in it
drop : (query : k) -> (xs : RecordM m k header) ->
       {auto loc : Label query header} ->
       RecordM m k (dropLabel header loc)
drop _ xs {loc} = dropByLabel xs loc

-- TRANSFORM

||| Project a record (keep only a subset of its field and reorder them.
|||
||| Complexity is _O(n)_
|||
project : RecordM m k header -> {auto prf : Sub sub header} -> RecordM m k sub
project (Rec xs nub) {prf = S prf} = Rec (project xs prf) (isNubFromSub prf nub)

||| Build a projection with the given keys
|||
||| @keys The rows to keep
||| @xs The record to project
||| @prf Proof that the rows are parts of the record
keep : (keys : List k) -> (xs : RecordM m k pre) ->
       {auto prf : SubWithKeys keys post pre} ->
       RecordM m k post
keep keys (Rec xs nub) {prf = S prf} =
  Rec (keep xs prf) (isNubFromSub (toSub prf) nub)

||| Build a projection that excludes the given keys
|||
||| @keys The rows to skip
||| @xs The record to project
||| @prf Proof that the rows are parts of the record
discard : (keys : List k) -> (xs : RecordM m k pre) ->
          {auto prf : CompWithKeys keys post pre} ->
          RecordM m k post
discard keys (Rec xs nub) {prf = S prf} =
  Rec (discard xs prf) (isNubFromSub (toSub prf) nub)

decLabel : DecEq k => (l : k) -> (xs : RecordM m k header) -> Dec (Label l header)
decLabel l _ {header} = decLabel l header

toTHList : RecordM m k header -> THList m k (toList header)
toTHList (Rec xs _) = toTHList xs


-- COMPARE

implementation
Eq (THList m k (toList header)) => Eq (RecordM m k header) where
  (==) xs ys = toTHList xs == toTHList ys
  (/=) xs ys = toTHList xs /= toTHList ys


-- SHOW

implementation
Show (THList m k (toList header)) => Show (RecordM m k header) where
  show xs = show (toTHList xs)
