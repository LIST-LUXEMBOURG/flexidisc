module CleanRecord.OrdList.Nub

import CleanRecord.Dec.IsYes
import CleanRecord.OrdList.Fresh
import CleanRecord.OrdList.Type
import CleanRecord.OrdList.Label

%default total
%access public export

data Nub : (OrdList label value o) -> Type where
  Nil  : Nub []
  (::) : Fresh l xs -> Nub xs -> Nub ((l,ty) :: xs)

||| Decide whether a list is made of different labelents or not
decNub : DecEq label => (xs : OrdList label value o) -> Dec (Nub xs)
decNub [] = Yes []
decNub ((l, ty) :: xs) with (decFresh l xs)
  | (Yes headFresh) with (decNub xs)
    | (Yes tailFresh) = Yes (headFresh :: tailFresh)
    | (No contra) = No (\ (_ :: tailFresh) => contra tailFresh)
  | (No contra) = No (\ (headFresh :: _) => contra headFresh)

IsNub : DecEq label => (xs : OrdList label value o) -> Type
IsNub xs = IsYes (decNub xs)

export
removeFromNubIsFresh : {k : key} ->
                       Nub xs -> (ePre : OrdLabel k xs) -> Fresh k (dropLabel xs ePre)
removeFromNubIsFresh (yes :: isnub) Here = yes
removeFromNubIsFresh (yes :: isnub) (There later) =
  (\p => freshCantBeLabel yes (rewrite (sym p) in later))
  :: removeFromNubIsFresh isnub later

export
dropPreservesFresh : Fresh l xs -> Fresh l (dropLabel xs e)
dropPreservesFresh (f :: fresh) {e = Here} = fresh
dropPreservesFresh (f :: fresh) {e = (There e)} = f :: dropPreservesFresh fresh

changeValuePreservesNub : Nub xs -> Nub (changeValue xs loc new)
changeValuePreservesNub [] {loc} = absurd loc
changeValuePreservesNub (p :: pf) {loc = Here} = p :: pf
changeValuePreservesNub (p :: pf) {loc = (There later)} =
  freshOnValueChange p :: changeValuePreservesNub pf

export
dropPreservesNub : Nub xs -> (loc : OrdLabel l xs) -> Nub (dropLabel xs loc)
dropPreservesNub (yes :: x) Here = x
dropPreservesNub (yes :: x) (There later) =
  dropPreservesFresh yes :: dropPreservesNub x later
