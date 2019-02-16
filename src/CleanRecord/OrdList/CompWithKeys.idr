module CleanRecord.OrdList.CompWithKeys

import CleanRecord.OrdList.Sub
import CleanRecord.OrdList.Type

import public Data.List

%default total

||| Proof that a vector is compose of the given keys and another vector.
|||
||| Used in `discard`, probably not useful anywhere else.
public export
data CompWithKeys : (keys : List k) ->
                   (xs : OrdList k v o) -> (ys : OrdList k v o) -> Type where
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
