module CleanRecord.OrdHeader.HereOrNot

import CleanRecord.Dec.IsYes
import CleanRecord.OrdHeader.Fresh
import CleanRecord.OrdHeader.Label
import CleanRecord.OrdHeader.Row
import CleanRecord.OrdHeader.Type

%default total
%access private

||| Proof that a `Vect` is a permutation of another vect
public export
data HereOrNot : (xs : OrdHeader k o1) -> (ys : OrdHeader k o2) -> Type where
  Empty : HereOrNot [] xs
  Skip  : DecEq k => {xs : OrdHeader k o} ->
          HereOrNot xs ys -> Fresh l xs -> HereOrNot ((l, ty) :: xs) ys
  Keep  : (loc : OrdRow l ty ys) -> HereOrNot xs ys -> HereOrNot ((l, ty) :: xs) ys

%name HereOrNot compat, can, prf
