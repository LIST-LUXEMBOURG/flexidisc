module CleanRecord.Header

import public CleanRecord.Header.CompWithKeys
import public CleanRecord.Header.Disjoint
import public CleanRecord.Header.Fresh
import public CleanRecord.Header.HereOrNot
import public CleanRecord.Header.Label
import public CleanRecord.Header.Nub
import public CleanRecord.Header.Row
import public CleanRecord.Header.Sub
import public CleanRecord.Header.SubWithKeys
import public CleanRecord.Header.Type

import CleanRecord.OrdHeader

%default total
%access public export

data SameOrd : (xs : Header k) -> (ys : Header k) -> Type where
  S : {xs : OrdHeader k o} -> {ys : OrdHeader k o} -> SameOrd xs ys -> SameOrd (H xs) (H ys)

diffKeys : DecEq k => (xs : Header k) -> (ys : Header k) -> Header k
diffKeys (H xs) (H ys) = H (diffKeys xs ys)
