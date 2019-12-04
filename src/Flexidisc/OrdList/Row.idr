module Flexidisc.OrdList.Row

import Flexidisc.OrdList.Label
import Flexidisc.OrdList.Type

%default total
%access public export

||| Proof that a key value pair is part of an `OrdList`. If you don't need the value, use `Label`.
data OrdRow : (l : k) -> (ty : v) -> OrdList k o v -> Type where
  ||| The label is in the first element of the list
  Here  :                             OrdRow l ty ((l, ty) :: xs)
  ||| The label is in the tail
  There : (later : OrdRow l ty xs) -> OrdRow l ty (x::xs)

%name OrdRow lbl, loc, prf, e, elem

||| Demote it to a label existence proof
labelFromOrdRow : OrdRow l v xs -> OrdLabel l xs
labelFromOrdRow Here          = Here
labelFromOrdRow (There later) = There (labelFromOrdRow later)

Uninhabited (OrdRow k v []) where
  uninhabited Here      impossible
  uninhabited (There _) impossible

||| Map a row and its header simultaneously
mapRow : {xs : OrdList k o a} -> (f : a -> b) -> (loc : OrdRow l ty xs) -> OrdRow l (f ty) (map f xs)
mapRow f loc {xs = []} = absurd loc
mapRow f Here {xs = ((k, x) :: xs)} = Here
mapRow f (There later) {xs = ((k, x) :: xs)} = There (mapRow f later)

||| Given a proof that an element is in a vector, remove it
dropOrdRow : (xs : OrdList k o v) -> (loc : OrdRow l ty xs) -> OrdList k o v
dropOrdRow xs = dropLabel xs . labelFromOrdRow

||| Update a value in the list given it's location and an update function
changeValue : (xs : OrdList k o v) -> (loc : OrdRow l old xs) -> (new : v) ->
             OrdList k o v
changeValue xs loc new = changeValue xs (labelFromOrdRow loc) new

changeWithSameTypeIsUnchanged : (row : OrdRow l x xs) -> changeValue xs row x = xs
changeWithSameTypeIsUnchanged Here = Refl
changeWithSameTypeIsUnchanged (There later) = cong $ changeWithSameTypeIsUnchanged later


findInsertOrdRow : (l : k) -> (xs : OrdList k o v) -> OrdRow l ty (insert (l,ty) xs)
findInsertOrdRow l [] = Here
findInsertOrdRow l ((kx, vx) :: xs) with (l < kx)
  | True  = Here
  | False = There (findInsertOrdRow l xs)

dropInsertInv : (l : k) -> (ty : v) -> (xs : OrdList k o v) ->
                dropOrdRow (insert (l, ty) xs) (findInsertOrdRow l xs) = xs
dropInsertInv l ty [] = Refl
dropInsertInv l ty ((kx,vx) :: xs) with (l < kx)
  | True  = Refl
  | False = cong (dropInsertInv l ty xs)
