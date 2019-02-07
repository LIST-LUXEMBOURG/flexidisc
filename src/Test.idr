module Test

import CleanRecord.Dec.IsYes
import CleanRecord.OrdHeader
import CleanRecord.RecordContent
import CleanRecord.TaggedValue
import CleanRecord.THList

import public CleanRecord.Header

%default total

data Record : (k : Type) -> Header k -> Type where
  Rec : (o : Ord k) => RecordContent k o header -> Nub header -> Record k (H header)

||| Build a `Record` from a list of values, the function checks unicity of
||| the fields and build the `Record` if such proof can be generated
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

get : Record k header -> (query : k) ->
      {auto loc : Label query header} -> atLabel header loc
get xs _ {loc} = atLabel xs loc

toTHList : Record k header -> THList (toList header)
toTHList (Rec xs _) = toTHList xs

implementation
Eq (THList (toList header)) => Eq (Record k header) where
  (==) xs ys = toTHList xs == toTHList ys
  (/=) xs ys = toTHList xs /= toTHList ys
