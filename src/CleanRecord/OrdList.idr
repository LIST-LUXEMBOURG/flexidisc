module CleanRecord.OrdList

import public CleanRecord.OrdList.CompWithKeys
import public CleanRecord.OrdList.Diff
import public CleanRecord.OrdList.Disjoint
import public CleanRecord.OrdList.HereOrNot
import public CleanRecord.OrdList.Fresh
import public CleanRecord.OrdList.Label
import public CleanRecord.OrdList.Nub
import public CleanRecord.OrdList.Permute
import public CleanRecord.OrdList.Sub
import public CleanRecord.OrdList.SubWithKeys
import public CleanRecord.OrdList.Type
import public CleanRecord.OrdList.Row

%default total
%access public export

data SameOrd : (xs : OrdList k v o) -> (ys : OrdList k v o) -> Type where
  Same : SameOrd xs ys

data Decomp : (required : OrdList k v o) -> (optional : OrdList k v o) -> (xs : OrdList k v o) -> Type where
  MkDecomp : Sub required xs -> HereOrNot optional xs -> Decomp required optional xs
