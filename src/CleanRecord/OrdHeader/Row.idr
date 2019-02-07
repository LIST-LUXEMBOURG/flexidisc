module CleanRecord.OrdHeader.Row

import CleanRecord.OrdHeader.Label
import CleanRecord.OrdHeader.Type

%default total
%access public export

||| Proof that a key value pair is part of a vector
data OrdRow : (l : k) -> (ty : Type) -> OrdHeader k o -> Type where
  Here  :                          OrdRow l ty ((l, ty) :: xs)
  There : (later : OrdRow l ty xs) -> OrdRow l ty (x::xs)

labelFromOrdRow : OrdRow k ty xs -> OrdLabel k xs
labelFromOrdRow Here          = Here
labelFromOrdRow (There later) = There (labelFromOrdRow later)

Uninhabited (OrdRow k v []) where
  uninhabited Here      impossible
  uninhabited (There _) impossible

||| Given a proof that an element is in a vector, remove it
dropOrdRow : (xs : OrdHeader k o) -> (loc : OrdRow l ty xs) -> OrdHeader k o
dropOrdRow xs = dropLabel xs . labelFromOrdRow

||| Update a value in the list given it's location and an update function
changeType : (xs : OrdHeader k o) -> (loc : OrdRow l old xs) -> (new : Type) ->
             OrdHeader k o
changeType xs loc new = changeType xs (labelFromOrdRow loc) new

findInsertOrdRow : (l : k) -> (xs : OrdHeader k o) -> OrdRow l ty (insert (l,ty) xs)
findInsertOrdRow l [] = Here
findInsertOrdRow l ((kx, vx) :: xs) with (l < kx)
  | True = Here
  | False = There (findInsertOrdRow l xs)

dropInsertInv : (l : k) -> (ty : Type) -> (xs : OrdHeader k o) ->
                dropOrdRow (insert (l, ty) xs) (findInsertOrdRow l xs) = xs
dropInsertInv l ty [] = Refl
dropInsertInv l ty ((kx,vx) :: xs) with (l < kx)
  | True = Refl
  | False = cong (dropInsertInv l ty xs)
