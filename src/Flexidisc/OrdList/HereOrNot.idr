module Flexidisc.OrdList.HereOrNot

import Flexidisc.Dec.IsYes
import Flexidisc.OrdList.Fresh
import Flexidisc.OrdList.Label
import Flexidisc.OrdList.Nub
import Flexidisc.OrdList.Row
import Flexidisc.OrdList.Sub
import Flexidisc.OrdList.Type

%default total

||| A proof that labels that are in both lists have the same values
public export
data HereOrNot : (xs : OrdList k v o) -> (ys : OrdList k v o) -> Type where
  ||| It holds for two empty `OrdList`
  Empty : HereOrNot [] []
  ||| If an element of the first list is not in the second list, it holds
  Skip  : DecEq k => {xs : OrdList k v o} -> HereOrNot xs ys -> IsFresh l ys -> HereOrNot ((l, ty) :: xs) ys
  ||| If an element of the second list is not in the first list, it holds
  Extra : DecEq k => {xs : OrdList k v o} -> HereOrNot xs ys -> IsFresh l xs -> HereOrNot xs ((l, ty) :: ys)
  ||| If an element is in both list, the values should be the same
  Keep  : HereOrNot xs ys -> HereOrNot ((l, ty) :: xs) ((l, ty) :: ys)

export
toRow : HereOrNot [(k, v)] ys -> Maybe (OrdRow k v ys)
toRow (Skip compat fresh)  = Nothing
toRow (Extra compat fresh) = There <$> toRow compat
toRow (Keep compat)        = Just Here

%name HereOrNot compat, can, prf

export
toSub : HereOrNot xs ys -> Maybe (Sub xs ys)
toSub Empty                = Just Empty
toSub (Skip compat fresh)  = Nothing
toSub (Extra compat fresh) = map Skip $ toSub compat
toSub (Keep compat)        = map Keep $ toSub compat
