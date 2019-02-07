module CleanRecord.OrdHeader.SubWithKeys

import CleanRecord.OrdHeader.Sub
import CleanRecord.OrdHeader.Type

import public Data.List

%default total

||| Proof that a `Vect` is a permutation of another vect
public export
data SubWithKeys : (keys : List k) ->
                   (xs : OrdHeader k o) -> (ys : OrdHeader k o) -> Type where
  Empty : SubWithKeys [] [] []
  Skip  : SubWithKeys keys xs ys -> SubWithKeys keys xs (y::ys)
  Keep  : (loc : Elem k keys) -> SubWithKeys (dropElem keys loc) xs ys ->
          SubWithKeys keys ((k, ty)::xs) ((k, ty)::ys)


%name SubWithKeys sub, issub, ss

export
toSub : SubWithKeys keys xs ys -> Sub xs ys
toSub Empty = Empty
toSub (Skip sub) = Skip (toSub sub)
toSub (Keep x sub) = Keep (toSub sub)
