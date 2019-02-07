module CleanRecord.Header.Nub

import CleanRecord.Header.Type
import CleanRecord.OrdHeader.Nub
import CleanRecord.OrdHeader.Type

%default total
%access public export

data Nub : (Header label) -> Type where
  N : (o : Ord k) => {xs : OrdHeader k o} -> Nub xs -> Nub (H xs)
