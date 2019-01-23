||| A proof that a `Vect` is an ordered subset of another `Vect`.
|||
||| It's quite similar to `OrdSub` but elements are removed from the original
||| set in an arbitrary chosen order.
|||
||| This one is used internally to discard a specific subset of keys of a
||| `Record`.
module CleanRecord.Relation.NegSub

import CleanRecord.Label
import CleanRecord.IsNo
import CleanRecord.Nub
import CleanRecord.Relation.OrdSub

import Data.Vect

%default total

||| Proof that a vector is a subset of another one,
||| preserving the order of the labels
public export
data NegSub : (sub : Vect n (key, value)) ->
           (initial : Vect m (key, value)) ->
           Type where
  Empty : NegSub [] []
  Skip  : (e : Label k initial) -> NegSub keep (dropLabel initial e) -> NegSub keep initial
  Keep  : NegSub sub initial -> NegSub ((k,v)::sub) ((k,v) :: initial)

||| An empty `Vect` is an ordered subset of any `Vect`
public export
subEmpty' : (xs : Vect n (key, value)) -> NegSub [] xs
subEmpty' [] = Empty
subEmpty' ((k,v) :: xs) = Skip Here (subEmpty' xs)

||| An empty `Vect` is an ordered subset of any `Vect`
public export
subEmpty : NegSub [] xs
subEmpty {xs} = subEmpty' xs

||| A `Vect` is an ordered subset of itself
public export
subRefl' : (xs : Vect n (key, value)) -> NegSub xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep (subRefl' xs)

||| A `Vect` is an ordered subset of itself
public export
subRefl : NegSub xs xs
subRefl {xs} = subRefl' xs

||| Given a proof that a label is in a `Vect` with one value dropped,
||| find its location in the original `Vect`
public export
shiftLabel :  (loc : Label k ys) -> Label x (dropLabel ys loc) -> Label x ys
shiftLabel Here label = There label
shiftLabel (There later) Here = Here
shiftLabel (There later) (There label) = There (shiftLabel later label)

||| `NegSub` preserves `label` proof
public export
labelFromNegSub : NegSub xs ys -> Label x xs -> Label x ys
labelFromNegSub Empty label = label
labelFromNegSub (Skip loc sub) label = shiftLabel loc (labelFromNegSub sub label)
labelFromNegSub (Keep x) Here = Here
labelFromNegSub (Keep sub) (There later) = There (labelFromNegSub sub later)


public export
notInNegSub : DecEq key =>
              {k: key} -> NegSub ys xs -> Not (Label k xs) -> NotLabel k ys
notInNegSub sub contra {k} {ys} with (decLabel k ys)
  | (Yes loc) = absurd (contra (labelFromNegSub sub loc))
  | (No _) = SoFalse

||| `NegSub` preserves nub-property
public export
isNubFromNegSub : NegSub xs ys -> IsNub ys -> IsNub xs
isNubFromNegSub Empty nub = nub
isNubFromNegSub (Skip e x) pf = isNubFromNegSub x (isNubFromOrdSub (ordSubFromDrop _ e) pf)
isNubFromNegSub (Keep x) (p :: pf) = notInNegSub x (getContra p) :: isNubFromNegSub x pf
