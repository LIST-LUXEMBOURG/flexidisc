module CleanRecord.Header.Row

import CleanRecord.Header.Type
import CleanRecord.OrdHeader.Type
import CleanRecord.OrdList.Row

%default total
%access public export

data Row : (k : l) -> (ty : Type) -> (xs : Header l) -> Type where
  R : {xs : OrdHeader l o} -> OrdRow k ty xs -> Row k ty (H xs)

%name Row lbl, loc, prf, e, elem

||| Given a proof that an element is in a vector, remove it
dropRow : (xs : Header k) -> (loc : Row l ty xs) -> Header k
dropRow (H xs) (R loc) = H (dropOrdRow xs loc)

||| Update a value in the list given it's location and an update function
changeType : (xs : Header k) -> (loc : Row l old xs) -> (new : Type) ->
             Header k
changeType (H xs) (R loc) = H . changeValue xs loc
