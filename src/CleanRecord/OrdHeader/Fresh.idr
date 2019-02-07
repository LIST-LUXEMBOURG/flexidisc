module CleanRecord.OrdHeader.Fresh

import CleanRecord.Dec.IsYes
import CleanRecord.OrdHeader.Type
import CleanRecord.OrdHeader.Label

%default total
%access public export

data Fresh : (l : label) -> (xs : OrdHeader label o) -> Type where
  Nil  : Fresh l []
  (::) : Not (l = l') -> Fresh l xs -> Fresh l ((l',ty') :: xs)

%name Fresh fresh, prf, new

decFresh : DecEq label => (l : label) -> (xs : OrdHeader label o) -> Dec (Fresh l xs)
decFresh l [] = Yes []
decFresh l ((l', ty) :: xs) with (decEq l l')
  | (Yes prf) = No (\ (freshHead :: _) => freshHead prf)
  | (No freshHere) with (decFresh l xs)
    | (Yes freshThere) = Yes (freshHere :: freshThere)
    | (No f) = No (\ (_ :: freshTail) => f freshTail)

IsFresh : DecEq label => (l : label) -> (xs : OrdHeader label o) -> Type
IsFresh l xs = IsYes (decFresh l xs)

export
freshOnTypeChange : Fresh l xs -> Fresh l (changeType xs loc new)
freshOnTypeChange (f :: fresh) {loc = Here} = f :: fresh
freshOnTypeChange (f :: fresh) {loc = (There later)} = f :: freshOnTypeChange fresh

export
freshCantBeLabel : Fresh l xs -> OrdLabel l xs -> Void
freshCantBeLabel (f :: fresh) Here = f Refl
freshCantBeLabel (f :: fresh) (There later) = freshCantBeLabel fresh later

export
isFreshFromEvidence : DecEq label => {l : label} -> (prf : Fresh l xs) -> IsFresh l xs
isFreshFromEvidence prf {l} {xs} with (decFresh l xs)
  | (Yes _) = SoTrue
  | (No contra) = absurd (contra prf)

export
tailIsFresh : DecEq label => {l : label} -> IsFresh l (x :: xs) -> IsFresh l xs
tailIsFresh x = case getProof x of (f :: fresh) => isFreshFromEvidence fresh
