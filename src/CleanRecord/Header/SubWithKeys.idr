module CleanRecord.Header.SubWithKeys

import CleanRecord.Header.Type
import CleanRecord.OrdHeader.SubWithKeys
import CleanRecord.OrdHeader.Type

%default total
%access public export

data SubWithKeys : (List k) -> (xs : Header k) -> (ys : Header k) -> Type where
  S : {xs : OrdHeader k o } -> {ys : OrdHeader k o } ->
      SubWithKeys keys xs ys -> SubWithKeys keys (H xs) (H ys)
