module CleanRecord.OrdList.HereOrNot

import CleanRecord.Dec.IsYes
import CleanRecord.OrdList.Fresh
import CleanRecord.OrdList.Label
import CleanRecord.OrdList.Row
import CleanRecord.OrdList.Sub
import CleanRecord.OrdList.Type

%default total

public export
data HereOrNot : (xs : OrdList k v o) -> (ys : OrdList k v o) -> Type where
  Empty : HereOrNot [] []
  Skip  : DecEq k => {xs : OrdList k v o} -> HereOrNot xs ys -> IsFresh l ys -> HereOrNot ((l, ty) :: xs) ys
  Extra : DecEq k => {xs : OrdList k v o} -> HereOrNot xs ys -> IsFresh l xs -> HereOrNot xs ((l, ty) :: ys)
  Keep  : HereOrNot xs ys -> HereOrNot ((l, ty) :: xs) ((l, ty) :: ys)

export
toRow : HereOrNot [(k, v)] ys -> Maybe (OrdRow k v ys)
toRow (Skip compat fresh) = Nothing
toRow (Extra compat fresh) = There <$> toRow compat
toRow (Keep compat) = Just Here

%name HereOrNot compat, can, prf

export
toSub : HereOrNot xs ys -> Maybe (Sub xs ys)
toSub Empty = Just Empty
toSub (Skip compat fresh) = Nothing
toSub (Extra compat fresh) = map Skip $ toSub compat
toSub (Keep compat) = map Keep $ toSub compat
