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

||| Create a record of Maybe type, with the values of the initial record,
||| if defined, or with `Nothing` if the field is not defined.
optional : DecEq k => (post : Header k) ->
           (xs : Record k header) ->
           {auto prf : HereOrNot post header} ->
           {default SoTrue postNub : IsNub post} ->
           RecordM Maybe k post
optional _ (Rec xs nubXS) {prf = HN prf} {postNub} =
  Rec (optional xs prf) (getProof postNub)

toTHList : RecordM m k header -> THList m k (toList header)
toTHList (Rec xs _) = toTHList xs

||| Change the effect
hoist : (f: {a : _} -> m a -> n a) -> (xs : RecordM m k header) -> RecordM n k header
hoist f (Rec xs nubXS) = Rec (hoist f xs) nubXS

||| Perform a `Record` transformation under the `Identity` Monad
withIdentity : (RecordM Identity k pre -> RecordM Identity k post) ->
               Record k pre -> Record k post
withIdentity f = hoist runIdentity . f . hoist Id

||| lift field of a Record
lift : (f: {a : _} -> a -> m a) -> (xs : Record k header) -> RecordM m k header
lift = hoist

||| extract an effect from a record
sequence : Applicative m => (xs : RecordM m k header) -> m (Record k header)
sequence (Rec xs nubXS) = flip Rec nubXS <$> sequence xs

||| embed the effect in the values, directly
unlift : RecordM m k header -> Record k (mapType m header)
unlift (Rec values nubProof) = Rec (unlift values) (mapValuesPreservesNub nubProof)

-- Foldmap

public export
data RecordFunc : (required : Header k) ->
                  (optional : Header k) ->
                  (result : Type) -> Type where
  Func : (Record k required -> RecordM Maybe k opt -> a) ->
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
Eq (THList m k (toList header)) => Eq (RecordM m k header) where
  (==) xs ys = toTHList xs == toTHList ys
  (/=) xs ys = toTHList xs /= toTHList ys


-- SHOW

implementation
Show (THList m k (toList header)) => Show (RecordM m k header) where
  show xs = show (toTHList xs)
