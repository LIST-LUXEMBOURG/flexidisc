module Flexidisc.OrdList.Nub

import Flexidisc.Dec.IsYes
import Flexidisc.OrdList.Fresh
import Flexidisc.OrdList.Type
import Flexidisc.OrdList.Label

%default total
%access public export

||| A proof that each value in the list has a different label
data Nub : (OrdList label value o) -> Type where
  ||| in an empty list, all the values are different indeed
  Nil  : Nub []
  ||| If we add a fresh value, it still holds
  (::) : Fresh l xs -> Nub xs -> Nub ((l,ty) :: xs)

%name Nub nub, isnub, prf

||| Decide whether a list is made of different labelents or not
decNub : DecEq label => (xs : OrdList label value o) -> Dec (Nub xs)
decNub [] = Yes []
decNub ((l, ty) :: xs) with (decFresh l xs)
  | (Yes headFresh) with (decNub xs)
    | (Yes tailFresh) = Yes (headFresh :: tailFresh)
    | (No contra) = No (\ (_ :: tailFresh) => contra tailFresh)
  | (No contra) = No (\ (headFresh :: _) => contra headFresh)

||| Proof that the decision procedure `decNub` gives a `Yes`
IsNub : DecEq label => (xs : OrdList label value o) -> Type
IsNub xs = IsYes (decNub xs)

||| If we remove a labelt from a `Nub` list, this label is `Fresh` for the
||| resulting list.
export
removeFromNubIsFresh : {k : key} ->
                       Nub xs -> (ePre : OrdLabel k xs) -> Fresh k (dropLabel xs ePre)
removeFromNubIsFresh (yes :: isnub) Here = yes
removeFromNubIsFresh (yes :: isnub) (There later) =
  (\p => freshCantBeLabel yes (rewrite (sym p) in later))
  :: removeFromNubIsFresh isnub later

||| `Nub` still hols if we change a value
changeValuePreservesNub : Nub xs -> Nub (changeValue xs loc new)
changeValuePreservesNub [] {loc} = absurd loc
changeValuePreservesNub (p :: pf) {loc = Here} = p :: pf
changeValuePreservesNub (p :: pf) {loc = (There later)} =
  freshOnValueChange p :: changeValuePreservesNub pf

||| If `Nub` holds for a list, it holds if we drop one element from the list
export
dropPreservesNub : Nub xs -> (loc : OrdLabel l xs) -> Nub (dropLabel xs loc)
dropPreservesNub (_   :: x) Here = x
dropPreservesNub (yes :: x) (There later) =
  dropPreservesFresh yes :: dropPreservesNub x later

mapValuesPreservesNub : Nub xs -> Nub (f <$> xs)
mapValuesPreservesNub [] = []
mapValuesPreservesNub (fresh :: nub) = freshOnMapValues fresh :: mapValuesPreservesNub nub
