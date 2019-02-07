module Test

import CleanRecord.Dec.IsYes
import CleanRecord.OrdHeader
import CleanRecord.RecordContent
import CleanRecord.TaggedValue
import CleanRecord.THList

import public CleanRecord.Header

%default total
%access export

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

atLabel : Record k header -> (loc : Label l header) -> atLabel header loc
atLabel (Rec xs _) (L loc) = atLabel xs loc

get : (query : k) -> Record k header ->
      {auto loc : Label query header} -> atLabel header loc
get query xs {loc} = atLabel xs loc

drop : (query : k) -> Record k header -> {auto prf : Label l header} ->
      Record k (dropLabel header prf)
drop query (Rec xs nub) {prf = L prf} =
  Rec (drop xs prf) (dropPreservesNub nub prf)

set : (query : k) -> (new : ty) -> Record k header ->
      {auto prf : Label l header} ->
      Record k (changeType header prf ty)
set query new (Rec xs nub) {prf = L prf} =
  Rec (set xs prf new) (changeTypePreservesNub nub)

infixl 7 !!

||| (Alomost) infix alias for `get`
(!!) : Record k header -> (query : k) ->
      {auto loc : Label query header} -> atLabel header loc
(!!) rec field = get field rec

project : Record k header -> {auto prf : Sub sub header} -> Record k sub
project (Rec xs nub) {prf = S prf} = Rec (project xs prf) (isNubFromSub prf nub)

toTHList : Record k header -> THList (toList header)
toTHList (Rec xs _) = toTHList xs

implementation
Eq (THList (toList header)) => Eq (Record k header) where
  (==) xs ys = toTHList xs == toTHList ys
  (/=) xs ys = toTHList xs /= toTHList ys
