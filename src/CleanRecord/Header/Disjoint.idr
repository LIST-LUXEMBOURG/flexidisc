module CleanRecord.Header.Disjoint

import CleanRecord.Header.Nub
import CleanRecord.Header.Type
import CleanRecord.OrdHeader.Disjoint
import CleanRecord.OrdHeader.Nub
import CleanRecord.OrdHeader.Type

%default total
%access public export

data Disjoint : (xs : Header k) -> (ys : Header k) -> Type where
  D : {xs : OrdHeader k o} -> {ys : OrdHeader k o} ->
      Disjoint xs ys -> Disjoint (H xs) (H ys)
