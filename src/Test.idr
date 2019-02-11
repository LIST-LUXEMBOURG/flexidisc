module Test

import CleanRecord.RecordContent
import public CleanRecord.THList

import public CleanRecord.OrdHeader
import public CleanRecord.Dec.IsYes
import public CleanRecord.Header
import public CleanRecord.TaggedValue

%default total
%access export

-- CREATE

||| A `Record` is a set of rows
||| @ k      The type of the labels
||| @ header The list of rows into the record, with their types
data Record : (k : Type) -> (header : Header k) -> Type where
  Rec : (o : Ord k) =>
        (values : RecordContent k o header) -> (nubProof : Nub header) ->
        Record k (H header)

infix 6 :::

||| Convenient helper for row type lisibility
public export
(:::) : (k : l) -> (v : Type) -> Pair l Type
(:::) = MkPair


%name Record xs, ys, zs

||| The empty record
Nil : Ord k => Record k []
Nil = Rec empty []

||| Insert a new row in a record
(::) : (DecEq k, Ord k) => TaggedValue k' ty -> Record k header ->
       {default SoTrue fresh : IsFresh k' header} ->
       Record k ((k',ty) :: header)
(::) x (Rec xs isnub) {fresh} =
  Rec (insert x xs) (freshInsert (getProof fresh) isnub)

private
test_rec1 : Record String ["Firstname" ::: String]
test_rec1 = ["Firstname" := "John"]

||| It's just monomorphic `id` with a fancy name, to help type inference
rec : Record k header -> Record k header
rec = id


-- READ

||| Get value from a `Row`
||| (not the most convenient way to get a value
||| but it may be useful when you have a `Row`)
|||
||| Complexity is _O(n)_
atRow : Record k header -> (loc : Row l ty header) -> ty
atRow (Rec xs _) (R loc) = atRow xs loc

||| Get value from a `Label`
||| (not the most convenient way to get a value
||| but it may be useful when you have a `Label`)
|||
||| It's slightly less efficient than `atRow`,
||| as you need to go through the header to get the return type
|||
||| Complexity is _O(n)_
atLabel : Record k header -> (loc : Label l header) -> atLabel header loc
atLabel (Rec xs _) (L loc) = atLabel xs loc

||| Typesafe extraction of a value from a record
|||
||| Complexity is _O(n)_
get : (query : k) -> Record k header ->
      {auto loc : Row query ty header} -> ty
get query xs {loc} = atRow xs loc

||| Typesafe extraction of a value from a record,
||| `Nothing` if the Row doesn't exist.
|||
||| Complexity is _O(n)_
export
lookup : (Ord k, DecEq k) =>
         (query : k) -> (xs : Record k header) ->
         {auto p : Header.HereOrNot.HereOrNot [(query, ty)] header} -> Maybe ty
lookup query xs {p} = case p of
  HN (Skip _ _) => Nothing
  HN (Keep loc x) => Just (atRow xs (R loc))


infixl 7 !!

||| (Almost) infix alias for `get`
|||
||| Almost: it requires an implicit paramet which may leads to weird behaviour
||| when used as an infix operator
(!!) : Record k header -> (query : k) ->
      {auto loc : Row query ty header} -> ty
(!!) rec field = get field rec

-- UPDATE

||| Replace a row, can change its type
|||
||| Complexity is _O(n)_
|||
||| @ xs  the record
||| @ loc the proof that the row is in it
||| @ new the new value for the row
setByLabel : (xs : Record k header) -> (loc : Label query header) -> (new : ty) ->
      Record k (changeType header loc ty)
setByLabel (Rec xs nub) (L loc) new =
  Rec (set xs loc new) (changeTypePreservesNub nub)

||| Update a row, the update can change the row type.
|||
||| Complexity is _O(n)_
|||
||| @ query the row name
||| @ xs    the record
||| @ loc   the proof that the row is in it
||| @ new   the new value for the row
set : (query : k) -> (new : ty) -> (xs : Record k header) ->
      {auto loc : Label query header} ->
      Record k (changeType header loc ty)
set _ new xs {loc} = setByLabel xs loc new

||| Update a row at a given `Row`, can change its type.
|||
||| Complexity is _O(n)_
|||
||| @ xs     the record
||| @ loc    the proof that the row is in it
||| @ f      the update function
updateByLabel : (xs : Record k header) -> (loc : Row query a header) ->
                (f : a -> b) ->
                Record k (changeType header loc b)
updateByLabel (Rec xs nub) (R loc) f =
  Rec (update xs loc f) (changeTypePreservesNub nub)

||| Update a row at a given `Row`, can change its type.
|||
||| Complexity is _O(n)_
|||
||| @ query  the row name
||| @ xs     the record
||| @ loc    the proof that the row is in it
||| @ f      the update function
update : (query : k) -> (f : a -> b) -> (xs : Record k header) ->
         {auto loc : Row query a header} ->
         Record k (changeType header loc b)
update _ f xs {loc} = updateByLabel xs loc f


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
        Record k (merge (diffKeys header' header) header)
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

toTHList : Record k header -> THList (toList header)
toTHList (Rec xs _) = toTHList xs


-- COMPARE

implementation
Eq (THList (toList header)) => Eq (Record k header) where
  (==) xs ys = toTHList xs == toTHList ys
  (/=) xs ys = toTHList xs /= toTHList ys
