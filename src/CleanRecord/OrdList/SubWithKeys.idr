module CleanRecord.OrdList.SubWithKeys

import CleanRecord.OrdList.Label
import CleanRecord.OrdList.Sub
import CleanRecord.OrdList.Type

import Data.List

import public Data.List

%default total

||| Proof that a `Vect` is a permutation of another vect
public export
data SubWithKeys : (keys : List k) ->
                   (xs : OrdList k v o) -> (ys : OrdList k v o) -> Type where
  Empty : SubWithKeys [] [] []
  Skip  : SubWithKeys keys xs ys -> SubWithKeys keys xs (y::ys)
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
