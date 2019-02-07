module CleanRecord.OrdHeader.CompWithKeys

import CleanRecord.OrdHeader.Sub
import CleanRecord.OrdHeader.Type

import public Data.List

%default total

||| Proof that a `Vect` is a permutation of another vect
public export
data CompWithKeys : (keys : List k) ->
                   (xs : OrdHeader k o) -> (ys : OrdHeader k o) -> Type where
  Empty : CompWithKeys [] [] []
  Skip  : (loc : Elem k keys) -> CompWithKeys (dropElem keys loc) xs ys ->
          CompWithKeys keys xs (y::ys)
  Keep  : CompWithKeys keys xs ys -> CompWithKeys keys ((k, ty)::xs) ((k, ty)::ys)


%name CompWithKeys sub, issub, ss

export
toSub : CompWithKeys keys xs ys -> Sub xs ys
toSub Empty = Empty
toSub (Skip x sub) = Skip (toSub sub)
toSub (Keep sub) = Keep (toSub sub)
