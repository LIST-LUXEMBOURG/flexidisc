module CleanRecord.Header.CompWithKeys

import CleanRecord.Header.Type
import CleanRecord.OrdHeader.CompWithKeys
import CleanRecord.OrdHeader.Type

%default total
%access public export

data CompWithKeys : (List k) -> (xs : Header k) -> (ys : Header k) -> Type where
  S : {xs : OrdHeader k o} -> {ys : OrdHeader k o} ->
      CompWithKeys keys xs ys -> CompWithKeys keys (H xs) (H ys)
