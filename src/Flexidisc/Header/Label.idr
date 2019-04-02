module Flexidisc.Header.Label

import Flexidisc.Header.Type
import Flexidisc.OrdHeader
import Flexidisc.OrdList.Label

%default total
%access public export

data Label : (l : k) -> (xs : Header k) -> Type where
  L : {xs : OrdHeader k o} -> OrdLabel l xs -> Label l (H xs)

%name Label lbl, loc, prf, e, elem

decLabel : DecEq k => (l : k) -> (xs : Header k) -> Dec (Label l xs)
decLabel l (H xs) with (decLabel l xs)
  | (Yes prf) = Yes (L prf)
  | (No contra) = No (\(L p) => contra p)

atLabel : (xs : Header l) -> (loc : Label k xs) -> Type
atLabel (H xs) (L loc) = atLabel xs loc

||| Given a proof that an element is in a vector, remove it
dropLabel : (xs : Header k) -> (loc : Label l xs) -> Header k
dropLabel (H xs) (L loc) = H (dropLabel xs loc)

||| Update a value in the list given it's location and an update function
changeType : (xs : Header k) -> (loc : Label l xs) -> (new : Type) -> Header k
changeType (H xs) (L loc) = H . changeType xs loc
