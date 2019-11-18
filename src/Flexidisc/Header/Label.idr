module Flexidisc.Header.Label

import Flexidisc.Header.Type
import Flexidisc.OrdList

%default total
%access public export

||| Proof that a label is in an `Header'`
data Label : (l : k) -> (xs : Header' k a) -> Type where
  ||| A wrapper for an `OrdLabel`
  L : {xs : OrdList k o a} -> OrdLabel l xs -> Label l (H xs)

%name Label lbl, loc, prf, e, elem

||| Decide whether a label is in a list or not
decLabel : DecEq k => (l : k) -> (xs : Header' k a) -> Dec (Label l xs)
decLabel l (H xs) with (decLabel l xs)
  | (Yes prf) = Yes (L prf)
  | (No contra) = No (\(L p) => contra p)

||| Given a proof that a label is in the list, get the corresponding value back
atLabel : (xs : Header' l a) -> (loc : Label k xs) -> a
atLabel (H xs) (L loc) = atLabel xs loc

||| Given a proof that an element is in a vector, remove it
dropLabel : (xs : Header' k a) -> (loc : Label l xs) -> Header' k a
dropLabel (H xs) (L loc) = H (dropLabel xs loc)

||| Update a value in the `Header'` given it's location and a new value
changeType : (xs : Header' k a) -> (loc : Label l xs) -> (new : a) ->
             Header' k a
changeType (H xs) (L loc) = H . changeValue xs loc
