module Flexidisc.OrdList.SubWithKeys

import Flexidisc.OrdList.Label
import Flexidisc.OrdList.Sub
import Flexidisc.OrdList.Type

import Data.List

import public Data.List

%default total

||| Proof that an `OrdList` has some given `keys` and is a sublist of an other
public export
data SubWithKeys : (keys : List k) ->
                   (xs : OrdList k v o) -> (ys : OrdList k v o) -> Type where
  ||| The empty `Ordlist` is a sublist of the empty `OrdList`
  Empty : SubWithKeys [] [] []
  ||| Making the second list larger don't change the property
  Skip  : SubWithKeys keys xs ys -> SubWithKeys keys xs (y::ys)
  ||| To add an element to the first list, we need to add it to the second one
  Keep  : (loc : Elem k keys) -> SubWithKeys (dropElem keys loc) xs ys ->
          SubWithKeys keys ((k, ty)::xs) ((k, ty)::ys)

Uninhabited (SubWithKeys (x::xs) sub []) where
  uninhabited Empty impossible
  uninhabited (Skip _) impossible
  uninhabited (Keep _ _) impossible

%name SubWithKeys sub, issub, ss

export
toSub : SubWithKeys keys xs ys -> Sub xs ys
toSub Empty = Empty
toSub (Skip sub) = Skip (toSub sub)
toSub (Keep x sub) = Keep (toSub sub)
