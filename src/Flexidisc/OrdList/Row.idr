module Flexidisc.OrdList.Row

import Flexidisc.OrdList.Label
import Flexidisc.OrdList.Type

%default total
%access public export

||| Proof that a key value pair is part of an `OrdList`
data OrdRow : (l : k) -> (ty : v) -> OrdList k v o -> Type where
  Here  :                          OrdRow l ty ((l, ty) :: xs)
  There : (later : OrdRow l ty xs) -> OrdRow l ty (x::xs)

%name OrdRow lbl, loc, prf, e, elem

||| Demote it to a label existence proof
labelFromOrdRow : OrdRow k v xs -> OrdLabel k xs
labelFromOrdRow Here          = Here
labelFromOrdRow (There later) = There (labelFromOrdRow later)

Uninhabited (OrdRow k v []) where
  uninhabited Here      impossible
  uninhabited (There _) impossible

||| Given a proof that an element is in a vector, remove it
dropOrdRow : (xs : OrdList k v o) -> (loc : OrdRow l ty xs) -> OrdList k v o
dropOrdRow xs = dropLabel xs . labelFromOrdRow

||| Update a value in the list given it's location and an update function
changeValue : (xs : OrdList k v o) -> (loc : OrdRow l old xs) -> (new : v) ->
             OrdList k v o
changeValue xs loc new = changeValue xs (labelFromOrdRow loc) new

changeWithSameTypeIsUnchanged : (row : OrdRow l x xs) -> changeValue xs row x = xs
changeWithSameTypeIsUnchanged Here = Refl
changeWithSameTypeIsUnchanged (There later) = cong $ changeWithSameTypeIsUnchanged later


findInsertOrdRow : (l : k) -> (xs : OrdList k v o) -> OrdRow l ty (insert (l,ty) xs)
findInsertOrdRow l [] = Here
findInsertOrdRow l ((kx, vx) :: xs) with (l < kx)
  | True = Here
  | False = There (findInsertOrdRow l xs)

dropInsertInv : (l : k) -> (ty : v) -> (xs : OrdList k v o) ->
                dropOrdRow (insert (l, ty) xs) (findInsertOrdRow l xs) = xs
dropInsertInv l ty [] = Refl
dropInsertInv l ty ((kx,vx) :: xs) with (l < kx)
  | True = Refl
  | False = cong (dropInsertInv l ty xs)
