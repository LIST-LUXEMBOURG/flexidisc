module Test

import CleanRecord.Dec.IsYes
import CleanRecord.OrdHeader
import CleanRecord.RecordContent
import CleanRecord.TaggedValue
import CleanRecord.THList

import public CleanRecord.Header

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

%name Record xs, ys, zs

||| The empty record
Nil : Ord k => Record k []
Nil = Rec empty []

||| Insert a new row in a record
(::) : (DecEq k, Ord k) => TaggedValue k' ty -> Record k header ->
       {default SoTrue fresh : IsFresh k' header} ->
       Record k ((k',ty) :: header)
(::) x (Rec xs isnub) {fresh} = Rec (insert x xs) (freshInsert fresh isnub)

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
      {auto loc : Label query header} -> atLabel header loc
get query xs {loc} = atLabel xs loc

infixl 7 !!

||| (Almost) infix alias for `get`
|||
||| Almost: it requires an implicit paramet which may leads to weird behaviour
||| when used as an infix operator
(!!) : Record k header -> (query : k) ->
      {auto loc : Label query header} -> atLabel header loc
(!!) rec field = get field rec

-- UPDATE

set : (query : k) -> (new : ty) -> Record k header ->
      {auto prf : Label query header} ->
      Record k (changeType header prf ty)
set query new (Rec xs nub) {prf = L prf} =
  Rec (set xs prf new) (changeTypePreservesNub nub)

update : (query : k) -> (f : a -> b) -> Record k header ->
         {auto prf : Row query a header} ->
         Record k (changeType header prf b)
update query f (Rec xs nub) {prf = R prf} =
  Rec (update xs prf f) (changeTypePreservesNub nub)

merge : {header : OrdHeader k o} -> {header' : OrdHeader k o} ->
        (xs : Record k (H header)) -> (ys : Record k (H header')) ->
        {auto prf : Disjoint header header'} ->
        Record k (H (merge header header'))
merge (Rec xs nubX) (Rec ys nubY) {o} {prf} =
  Rec (merge xs ys) (disjointNub prf nubX nubY)

(++) : {header : OrdHeader k o} -> {header' : OrdHeader k o} ->
       (xs : Record k (H header)) -> (ys : Record k (H header')) ->
       {auto prf : Disjoint header header'} ->
       Record k (H (merge header header'))
(++) = merge

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

project : Record k header -> {auto prf : Sub sub header} -> Record k sub
project (Rec xs nub) {prf = S prf} = Rec (project xs prf) (isNubFromSub prf nub)

keep : (keys : List k) -> (xs : Record k pre) ->
       {auto prf : SubWithKeys keys post pre} ->
       Record k post
keep keys (Rec xs nub) {prf = S prf} =
  Rec (keep xs prf) (isNubFromSub (toSub prf) nub)

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
