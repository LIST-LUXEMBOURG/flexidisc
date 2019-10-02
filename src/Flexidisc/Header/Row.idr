module Flexidisc.Header.Row

import Flexidisc.Header.Type
import Flexidisc.OrdList
import Flexidisc.OrdList.Row

%default total
%access public export

data Row : (k : l) -> (ty : a) -> (xs : Header' l a) -> Type where
  R : {xs : OrdList l o a} -> OrdRow k ty xs -> Row k ty (H xs)

%name Row lbl, loc, prf, e, elem

||| Given a proof that an element is in a vector, remove it
dropRow : (xs : Header' k a) -> (loc : Row l ty xs) -> Header' k a
dropRow (H xs) (R loc) = H (dropOrdRow xs loc)

||| Update a value in the list given it's location and an update function
changeType : (xs : Header' k a) -> (loc : Row l old xs) ->
             (new : a) -> Header' k a
changeType (H xs) (R loc) = H . changeValue xs loc
