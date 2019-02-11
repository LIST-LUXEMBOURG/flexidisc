module CleanRecord.Header.Label

import CleanRecord.Header.Type
import CleanRecord.OrdHeader.Label
import CleanRecord.OrdHeader.Type
import CleanRecord.OrdList.Label

%default total
%access public export

data Label : (k : l) -> (xs : Header l) -> Type where
  L : {xs : OrdHeader l o} -> OrdLabel k xs -> Label k (H xs)

%name Label lbl, loc, prf, e, elem

atLabel : (xs : Header l) -> (loc : Label k xs) -> Type
atLabel (H xs) (L loc) = atLabel xs loc

||| Given a proof that an element is in a vector, remove it
dropLabel : (xs : Header k) -> (loc : Label l xs) -> Header k
dropLabel (H xs) (L loc) = H (dropLabel xs loc)

||| Update a value in the list given it's location and an update function
changeType : (xs : Header k) -> (loc : Label l xs) -> (new : Type) -> Header k
changeType (H xs) (L loc) = H . changeType xs loc
