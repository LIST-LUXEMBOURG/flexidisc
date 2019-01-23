||| Define proof that a Vect contains a subset of the element of another Vect
module CleanRecord.Relation.Sub

import CleanRecord.IsNo
import CleanRecord.Label
import CleanRecord.Nub
import CleanRecord.Relation.OrdSub
import CleanRecord.Row

import Data.Vect

%default total


||| Proof thet a `Vect` is a subset of another `Vect`
||| @ sub the suset
||| @ initial the original `Vect`
public export
data Sub : (sub : Vect n (key, value)) ->
           (initial : Vect m (key, value)) ->
           Type where
  Empty : Sub [] []
  Skip  : Sub sub initial -> Sub sub ((k,v) :: initial)
  Keep  : (e : Row k v initial) -> Sub keep (dropRow initial e) -> Sub ((k,v)::keep) initial

||| An empty `Vect` is an ordered subset of any `Vect`
public export
subEmpty' : (xs : Vect n (key, value)) -> Sub [] xs
subEmpty' [] = Empty
subEmpty' ((k, v) :: xs) = Skip (subEmpty' xs)

||| An empty `Vect` is an ordered subset of any `Any`
public export
subEmpty : Sub [] xs
subEmpty {xs} = subEmpty' xs

||| A `Vect` is an ordered subset of itself
public export
subRefl' : (xs : Vect n (key, value)) -> Sub xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep Here (subRefl' xs)

||| A `Vect` is an ordered subset of itself
public export
subRefl : Sub xs xs
subRefl {xs} = subRefl' xs

||| Given the proof that a Label is in an subset of a vect
||| provide a proof that this label is in the initial vect
public export
labelFromSub : Sub xs ys -> Label x xs -> Label x ys
labelFromSub Empty y = y
labelFromSub (Skip z) loc = There (labelFromSub z loc)
labelFromSub (Keep e _) Here = labelFromRow e
labelFromSub (Keep e sub) (There later) = labelFromDrop (labelFromSub sub later)

||| If a label is not in the initial vector, it can't be in a
||| subset of this vect
public export
notInSub : DecEq key =>
           {k: key} -> Sub ys xs -> Not (Label k xs) -> NotLabel k ys
notInSub sub contra {k} {ys} with (decLabel k ys)
  | (Yes loc) = absurd (contra (labelFromSub sub loc))
  | (No _) = SoFalse


||| If the original vector doesn't contain any duplicate,
||| a subset doesn't contain duplicate as well
public export
isNubFromSub : Sub xs ys -> IsNub ys -> IsNub xs
isNubFromSub Empty [] = []
isNubFromSub (Skip z) (_ :: pf) = isNubFromSub z pf
isNubFromSub (Keep e z) (p :: pf) = let
  eAsLabel = labelFromRow e
  in notInSub z (removeFromNubIsNotThere (p::pf) eAsLabel)
     :: isNubFromSub z (isNubFromOrdSub (ordSubFromDrop _ eAsLabel) (p::pf))
