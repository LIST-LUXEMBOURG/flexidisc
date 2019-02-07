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

data Record : (k : Type) -> Header k -> Type where
  Rec : (o : Ord k) =>
        RecordContent k o header -> Nub header -> Record k (H header)

%name Record xs, ys, zs

rec : (xs : RecordContent k o header) -> {auto nubProof : Nub header} ->
      Record k (H header)
rec xs {nubProof} = Rec xs nubProof

Nil : Ord k => Record k []
Nil = Rec [] []

(::) : (DecEq k, Ord k) => TaggedValue k' ty -> Record k header ->
       {default SoTrue fresh : IsFresh k' header} ->
       Record k ((k',ty) :: header)
(::) x (Rec xs isnub) {fresh} = Rec (x :: xs) (freshInsert fresh isnub)

-- READ

atLabel : Record k header -> (loc : Label l header) -> atLabel header loc
atLabel (Rec xs _) (L loc) = atLabel xs loc

get : (query : k) -> Record k header ->
      {auto loc : Label query header} -> atLabel header loc
get query xs {loc} = atLabel xs loc

infixl 7 !!

||| (Alomost) infix alias for `get`
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

-- DELETE

drop : (query : k) -> Record k header -> {auto prf : Label query header} ->
      Record k (dropLabel header prf)
drop query (Rec xs nub) {prf = L prf} =
  Rec (drop xs prf) (dropPreservesNub nub prf)

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
