||| Define proof that a List contains a subset of the element of another List
module CleanRecord.Relation.Sub

import CleanRecord.Elem.Label
import CleanRecord.Elem.Row
import CleanRecord.IsNo
import CleanRecord.Nub

%default total
%access public export


||| Proof thet a `List` is a subset of another `List`
||| @ sub the suset
||| @ initial the original `List`
data Sub : (sub : List (key, value)) ->
           (initial : List (key, value)) ->
           Type where
  Empty : Sub [] []
  Skip  : Sub sub initial -> Sub sub ((k,v) :: initial)
  Keep  : (e : Row k v initial) -> Sub keep (dropRow initial e) -> Sub ((k,v)::keep) initial

||| An empty `List` is an ordered subset of any `List`
subEmpty' : (xs : List (key, value)) -> Sub [] xs
subEmpty' [] = Empty
subEmpty' ((k, v) :: xs) = Skip (subEmpty' xs)

||| An empty `List` is an ordered subset of any `List`
subEmpty : Sub [] xs
subEmpty {xs} = subEmpty' xs

||| A `List` is an ordered subset of itself
subRefl' : (xs : List (key, value)) -> Sub xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep Here (subRefl' xs)

||| A `List` is an ordered subset of itself
subRefl : Sub xs xs
subRefl {xs} = subRefl' xs

||| Given the proof that a Label is in an subset of a vect
||| provide a proof that this label is in the initial vect
%hint
labelFromSub : Sub xs ys -> Label x xs -> Label x ys
labelFromSub Empty y = y
labelFromSub (Skip z) loc = There (labelFromSub z loc)
labelFromSub (Keep e _) Here = labelFromRow e
labelFromSub (Keep e sub) (There later) = labelFromDrop (labelFromSub sub later)

||| Given the proof that a Label is in an subset of a vect
||| provide a proof that this label is in the initial vect
%hint
rowFromSub : Sub xs ys -> Row key ty xs -> Row key ty ys
rowFromSub Empty y = y
rowFromSub (Skip z) loc = There (rowFromSub z loc)
rowFromSub (Keep e _) Here = e
rowFromSub (Keep e sub) (There later) = rowFromDrop (rowFromSub sub later)

||| If a label is not in the initial vector, it can't be in a
||| subset of this vect
notInSub : DecEq key =>
           {k: key} -> Sub ys xs -> Not (Label k xs) -> NotLabel k ys
notInSub sub contra {k} {ys} with (decLabel k ys)
  | (Yes loc) = absurd (contra (labelFromSub sub loc))
  | (No _) = SoFalse


||| If the original vector doesn't contain any duplicate,
||| a subset doesn't contain duplicate as well
isNubFromSub : Sub xs ys -> IsNub ys -> IsNub xs
isNubFromSub Empty [] = []
isNubFromSub (Skip z) (_ :: pf) = isNubFromSub z pf
isNubFromSub (Keep e z) (p :: pf) = let
  eAsLabel = labelFromRow e
  in notInSub z (removeFromNubIsNotThere (p::pf) eAsLabel)
     :: isNubFromSub z (dropPreservesNub (p::pf))
