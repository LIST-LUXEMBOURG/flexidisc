module CleanRecord.OrdList.HereOrNot

import CleanRecord.Dec.IsYes
import CleanRecord.OrdList.Fresh
import CleanRecord.OrdList.Label
import CleanRecord.OrdList.Row
import CleanRecord.OrdList.Type

%default total
%access private

||| Proof that a `Vect` is a permutation of another vect
public export
data HereOrNot : (xs : OrdList k v o1) -> (ys : OrdList k v o2) -> Type where
  Empty : HereOrNot [] xs
  Skip  : DecEq k => {xs : OrdList k v o} ->
          HereOrNot xs ys -> Fresh l xs -> HereOrNot ((l, ty) :: xs) ys
  Keep  : (loc : OrdRow l ty ys) -> HereOrNot xs ys -> HereOrNot ((l, ty) :: xs) ys

%name HereOrNot compat, can, prf
