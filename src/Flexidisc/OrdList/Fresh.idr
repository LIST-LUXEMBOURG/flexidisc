module Flexidisc.OrdList.Fresh

import Flexidisc.Dec.IsYes
import Flexidisc.OrdList.Type
import Flexidisc.OrdList.Label

%default total
%access public export

||| Proof that a label is not in an `OrdList`
data Fresh : (l : label) -> (xs : OrdList label value o) -> Type where
  Nil  : Fresh l []
  (::) : Not (l = l') -> Fresh l xs -> Fresh l ((l',ty') :: xs)

%name Fresh fresh, prf, new

||| Decide whether a label is fresh or not
decFresh : DecEq label => (l : label) -> (xs : OrdList label value o) -> Dec (Fresh l xs)
decFresh l [] = Yes []
decFresh l ((l', ty) :: xs) with (decEq l l')
  | (Yes prf) = No (\ (freshHead :: _) => freshHead prf)
  | (No freshHere) with (decFresh l xs)
    | (Yes freshThere) = Yes (freshHere :: freshThere)
    | (No f) = No (\ (_ :: freshTail) => f freshTail)

||| Ensure that the result of `decFresh` is a `Yes` for a given label and a
||| given `OrdList`
IsFresh : DecEq label => (l : label) -> (xs : OrdList label value o) -> Type
IsFresh l xs = IsYes (decFresh l xs)

||| Changing a value doesn't impact the freshness of a label
freshOnValueChange : Fresh l xs -> Fresh l (changeValue xs loc new)
freshOnValueChange (f :: fresh) {loc = Here} = f :: fresh
freshOnValueChange (f :: fresh) {loc = (There later)} = f :: freshOnValueChange fresh

||| Changing values doesn't impact the freshness of a label
freshOnMapValues : (p : Fresh l xs) -> Fresh l (mapValues f xs)
freshOnMapValues [] = []
freshOnMapValues (prf :: fresh) = prf :: freshOnMapValues fresh

||| We can't find a label that is `Fresh` in an `OrdList`
freshCantBeLabel : Fresh l xs -> Not (OrdLabel l xs)
freshCantBeLabel (f :: fresh) Here = f Refl
freshCantBeLabel (f :: fresh) (There later) = freshCantBeLabel fresh later

||| If a label is not in a list, is not in this list minus one element.
export
dropPreservesFresh : Fresh l xs -> Fresh l (dropLabel xs e)
dropPreservesFresh (f :: fresh) {e = Here} = fresh
dropPreservesFresh (f :: fresh) {e = (There e)} = f :: dropPreservesFresh fresh

||| If we can exhibit a `Fresh` value, we can build an `IsFresh` proof
isFreshFromEvidence : DecEq label => {l : label} -> (prf : Fresh l xs) -> IsFresh l xs
isFreshFromEvidence prf {l} {xs} with (decFresh l xs)
  | (Yes _) = SoTrue
  | (No contra) = absurd (contra prf)

||| If a label is not in an `OrdList`, it's not in the tail either
tailIsFresh : DecEq label => {l : label} -> IsFresh l (x :: xs) -> IsFresh l xs
tailIsFresh x = case getProof x of (f :: fresh) => isFreshFromEvidence fresh
