||| `OrdList` is a "labelled" list that ensure that inserted elements are ordered.
module Flexidisc.OrdList

import public Flexidisc.OrdList.CompWithKeys
import public Flexidisc.OrdList.Diff
import public Flexidisc.OrdList.Disjoint
import public Flexidisc.OrdList.HereOrNot
import public Flexidisc.OrdList.Fresh
import public Flexidisc.OrdList.Label
import public Flexidisc.OrdList.Nub
import public Flexidisc.OrdList.Permute
import public Flexidisc.OrdList.Sub
import public Flexidisc.OrdList.SubWithKeys
import public Flexidisc.OrdList.Type
import public Flexidisc.OrdList.Row

%default total
%access public export

||| A witness that two OrdList are using the same order
||| (as well as the same key and value type, but this is more obvious)
data SameOrd : (xs, ys : OrdList k v o) -> Type where
  Same : SameOrd xs ys
