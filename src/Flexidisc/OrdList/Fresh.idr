module Flexidisc.OrdList.Fresh

import Flexidisc.Dec.IsYes
import Flexidisc.OrdList.Type
import Flexidisc.OrdList.Label

%default total
%access public export

||| Proof that a key is not in an `OrdList`
data Fresh : (l : key) -> (xs : OrdList key o value) -> Type where
  ||| It's always fresh when the `Ordlist` is empty
  Nil  : Fresh l []
  ||| If it's not the head nor in the tail, then it's `Fresh`
  (::) : Not (l = l') -> Fresh l xs -> Fresh l ((l',ty') :: xs)

%name Fresh fresh, prf, new

||| Decide whether a label is fresh or not
decFresh : DecEq key => (l : key) -> (xs : OrdList key o value) -> Dec (Fresh l xs)
decFresh l [] = Yes []
decFresh l ((l', ty) :: xs) with (decEq l l')
  | (Yes prf) = No (\ (freshHead :: _) => freshHead prf)
  | (No freshHere) with (decFresh l xs)
    | (Yes freshThere) = Yes (freshHere :: freshThere)
    | (No f) = No (\ (_ :: freshTail) => f freshTail)

||| Ensure that the result of `decFresh` is a `Yes` for a given label and a
||| given `OrdList`
IsFresh : DecEq key => (l : key) -> (xs : OrdList key o value) -> Type
IsFresh l xs = IsYes (decFresh l xs)

||| Changing a value doesn't impact the freshness of a label
freshOnValueChange : Fresh l xs -> Fresh l (changeValue xs loc new)
freshOnValueChange (f :: fresh) {loc = Here} = f :: fresh
freshOnValueChange (f :: fresh) {loc = (There later)} = f :: freshOnValueChange fresh

||| Changing values doesn't impact the freshness of a label
freshOnMapValues : (p : Fresh l xs) -> Fresh l (f <$> xs)
freshOnMapValues [] = []
freshOnMapValues (prf :: fresh) = prf :: freshOnMapValues fresh

||| We can't find a label that is `Fresh` in an `OrdList`
freshCantBeLabel : Fresh l xs -> Not (OrdLabel l xs)
freshCantBeLabel (f :: _    ) Here = f Refl
freshCantBeLabel (_ :: fresh) (There later) = freshCantBeLabel fresh later

||| If a label is not in a list, is not in this list minus one element.
export
dropPreservesFresh : Fresh l xs -> Fresh l (dropLabel xs e)
dropPreservesFresh (f :: fresh) {e = Here} = fresh
dropPreservesFresh (f :: fresh) {e = (There e)} = f :: dropPreservesFresh fresh

||| If we can exhibit a `Fresh` value, we can build an `IsFresh` proof
isFreshFromEvidence : DecEq key => {l : key} -> (prf : Fresh l xs) -> IsFresh l xs
isFreshFromEvidence prf {l} {xs} with (decFresh l xs)
  | (Yes _) = SoTrue
  | (No contra) = absurd (contra prf)

||| If a label is not in an `OrdList`, it's not in the tail either
tailIsFresh : DecEq key => {l : key} -> IsFresh l (x :: xs) -> IsFresh l xs
tailIsFresh x = case getProof x of (f :: fresh) => isFreshFromEvidence fresh
