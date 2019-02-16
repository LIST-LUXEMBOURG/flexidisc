module CleanRecord.Header.Sub

import CleanRecord.Header.Label
import CleanRecord.Header.Row
import CleanRecord.Header.Type
import CleanRecord.OrdList.Label
import CleanRecord.OrdList.Row
import CleanRecord.OrdList.Sub
import CleanRecord.OrdHeader

%default total
%access public export

data Sub : (xs : Header k) -> (ys : Header k) -> Type where
  S : {xs : OrdHeader k o } -> {ys : OrdHeader k o } ->
      Sub xs ys -> Sub (H xs) (H ys)

%hint
public export
rowFromSub : Sub xs ys -> Row key ty xs -> Row key ty ys
rowFromSub (S sub) (R lbl) = R (rowFromSub sub lbl)

%hint
public export
labelFromSub : Sub xs ys -> Label x xs -> Label x ys
labelFromSub (S sub) (L lbl) = L (labelFromSub sub lbl)
