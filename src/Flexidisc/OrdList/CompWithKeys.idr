module Flexidisc.OrdList.CompWithKeys

import Flexidisc.OrdList.Sub
import Flexidisc.OrdList.Type

import public Data.List

%default total

||| Proof that an `Ordlist` is composed of the given keys and another `OrdList`.
|||
||| Used in `discard`, probably not useful anywhere else.
public export
data CompWithKeys : (keys : List k) -> (xs, ys : OrdList k v o) -> Type where
  ||| Both `OrdList`s are empty
  Empty : CompWithKeys [] [] []
  ||| The second `OrdList` contains an extra key, that is not in the first `OrdList`
  Skip  : (loc : Elem k keys) -> CompWithKeys (dropElem keys loc) xs ys ->
          CompWithKeys keys xs (y::ys)
  ||| An element is shared bit both `OrdList`s
  Keep  : CompWithKeys keys xs ys -> CompWithKeys keys ((k, ty)::xs) ((k, ty)::ys)

%name CompWithKeys sub, issub, ss

||| Map a `CompWithKeys` to a `Sub`
export
toSub : CompWithKeys keys xs ys -> Sub xs ys
toSub Empty        = Empty
toSub (Skip x sub) = Skip (toSub sub)
toSub (Keep sub)   = Keep (toSub sub)
