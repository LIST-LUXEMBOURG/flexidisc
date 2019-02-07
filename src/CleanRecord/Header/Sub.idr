module CleanRecord.Header.Sub

import CleanRecord.Header.Type
import CleanRecord.OrdHeader.Sub
import CleanRecord.OrdHeader.Type

%default total
%access public export

data Sub : (xs : Header k) -> (ys : Header k) -> Type where
  S : {xs : OrdHeader k o } -> {ys : OrdHeader k o } ->
      Sub xs ys -> Sub (H xs) (H ys)
