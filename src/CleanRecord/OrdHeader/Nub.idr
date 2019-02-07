module CleanRecord.OrdHeader.Nub

import CleanRecord.Dec.IsYes
import CleanRecord.OrdHeader.Fresh
import CleanRecord.OrdHeader.Type
import CleanRecord.OrdHeader.Label

%default total
%access public export

data Nub : (OrdHeader label o) -> Type where
  Nil  : Nub []
  (::) : DecEq k => {l : k} -> IsFresh l xs -> Nub xs -> Nub ((l,ty) :: xs)

||| Decide whether a list is made of different labelents or not
decNub : DecEq label => (xs : OrdHeader label o) -> Dec (Nub xs)
decNub [] = Yes []
decNub ((l, ty) :: xs) with (decFresh l xs)
  | (Yes headFresh) with (decNub xs)
    | (Yes tailFresh) = Yes (isFreshFromEvidence headFresh :: tailFresh)
    | (No contra) = No (\ (_ :: tailFresh) => contra tailFresh)
  | (No contra) = No (\ (headFresh :: _) => contra (getProof headFresh))

IsNub : DecEq label => (xs : OrdHeader label o) -> Type
IsNub xs = IsYes (decNub xs)

export
removeFromNubIsFresh : {k : key} ->
                       Nub xs -> (ePre : OrdLabel k xs) -> Fresh k (dropLabel xs ePre)
removeFromNubIsFresh (yes :: isnub) Here = getProof yes
removeFromNubIsFresh (yes :: isnub) (There later) =
  (\p => freshCantBeLabel (getProof yes) (rewrite (sym p) in later))
  :: removeFromNubIsFresh isnub later

export
dropPreservesFresh : Fresh l xs -> Fresh l (dropLabel xs e)
dropPreservesFresh (f :: fresh) {e = Here} = fresh
dropPreservesFresh (f :: fresh) {e = (There e)} = f :: dropPreservesFresh fresh

changeTypePreservesNub : Nub xs -> Nub (changeType xs loc new)
changeTypePreservesNub [] {loc} = absurd loc
changeTypePreservesNub (p :: pf) {loc = Here} = p :: pf
changeTypePreservesNub (p :: pf) {loc = (There later)} =
  isFreshFromEvidence (freshOnTypeChange (getProof p)) :: changeTypePreservesNub pf

export
dropPreservesNub : Nub xs -> (loc : OrdLabel l xs) -> Nub (dropLabel xs loc)
dropPreservesNub (yes :: x) Here = x
dropPreservesNub (yes :: x) (There later) =
  isFreshFromEvidence (dropPreservesFresh (getProof yes)) :: dropPreservesNub x later
