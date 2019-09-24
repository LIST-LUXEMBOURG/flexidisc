module Flexidisc.Record

import        Flexidisc.RecordContent

import public Flexidisc.Dec.IsYes
import public Flexidisc.Header
import public Flexidisc.OrdHeader
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


||| Patch the right-hand side record with the values on the left-hand side
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

||| Create a record of Maybe type, with the values of the initial record,
||| if defined, or with `Nothing` if the field is not defined.
optional : DecEq k => (post : Header k) ->
           (xs : Record k header) ->
           {auto prf : HereOrNot post header} ->
           {default SoTrue postNub : IsNub post} ->
           Record k (optional post)
optional _ (Rec xs nubXS) {prf = HN prf} {postNub} =
  Rec (optional xs prf) (mapValuesPreservesNub (getProof postNub))

toTHList : Record k header -> THList k (toList header)
toTHList (Rec xs _) = toTHList xs

-- Foldmap

public export
data RecordFunc : (required : Header k) -> (optional : Header k) ->
                  (reasult : Type) -> Type where
  Func : (Record k required -> Record k (optional opt) -> a) ->
         RecordFunc required opt a

||| Apply a function on a known set of data
foldRecord : (Ord k, DecEq k) =>
             RecordFunc required opt a ->
             Record k header ->
             {auto optNub : IsNub opt} ->
             {auto decomp : Decomp required opt header} ->
             a
foldRecord (Func f) xs {opt} {decomp = D sub op} {optNub} =
  f (project xs) (optional opt xs {postNub = optNub})




-- COMPARE

implementation
Eq (THList k (toList header)) => Eq (Record k header) where
  (==) xs ys = toTHList xs == toTHList ys
  (/=) xs ys = toTHList xs /= toTHList ys


-- SHOW

implementation
Show (THList k (toList header)) => Show (Record k header) where
  show xs = show (toTHList xs)
