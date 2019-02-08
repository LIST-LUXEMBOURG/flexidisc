module CleanRecord.Header.HereOrNot

import CleanRecord.Header.Type
import CleanRecord.OrdHeader.HereOrNot
import CleanRecord.OrdHeader.Type

%default total
%access public export

data HereOrNot : (xs : Header k) -> (ys : Header k) -> Type where
  HN : {xs : OrdHeader k o} -> {ys : OrdHeader k o} ->
       HereOrNot xs ys -> HereOrNot (H xs) (H ys)
