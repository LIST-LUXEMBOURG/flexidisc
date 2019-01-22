module CleanRecord.Row

import Data.Vect

import CleanRecord.IsNo
import public CleanRecord.Label

%default total
%access public export

||| Proof that a key value pair is part of a vector
data Row : (k : key) -> (v : value) -> Vect n (key, value) -> Type where
  Here : Row k v ((k, v) :: xs)
  There : (later : Row k v xs) -> Row k v (x::xs)

%name Row row, loc, prf, e, elem

rowFromElem : Elem (k, v) xs -> Row k v xs
rowFromElem Here = Here
rowFromElem (There later) = There (rowFromElem later)

elemFromRow : Row k v xs -> Elem (k, v) xs
elemFromRow Here = Here
elemFromRow (There later) = There (elemFromRow later)

labelFromRow : Row k v xs -> Label k xs
labelFromRow Here = Here
labelFromRow (There later) = There (labelFromRow later)

Uninhabited (Row k v []) where
  uninhabited Here impossible
  uninhabited (There _) impossible

||| Given a proof that an element is in a vector, remove it
dropRow : (xs : Vect (S n) (key, value)) -> (loc : Row k v xs) ->
          Vect n (key, value)
dropRow xs = dropLabel xs . labelFromRow

||| Update a value in the list given it's location and an update function
updateRow : (xs : Vect n (key, value)) -> (loc : Row k old xs) ->
             (new : value) -> Vect n (key, value)
updateRow xs loc new = updateLabel xs (labelFromRow loc) new

||| Given a proof that an element is in a list with one element dropped
||| find its location in the original list.
rowFromDrop : {xs : Vect (S n) (key, value)} -> {loc : Row k' v' xs} ->
               Row k v (dropRow xs loc) -> Row k v xs
rowFromDrop prf         {loc = Here}          = There prf
rowFromDrop Here        {loc = (There later)} = Here
rowFromDrop (There loc) {loc = (There later)} = There (rowFromDrop loc)

||| Decide whether a key is in a vector or not
decKey : DecEq key =>
         (k : key) -> (xs : Vect n (key, value)) ->
         Dec (v ** Row k v xs)
decKey _   [] = No (\pf => absurd (snd pf))
decKey k ((k', v') :: xs) with (decEq k k')
  | (Yes prf) = rewrite prf in Yes (v' ** Here)
  | (No notHere) with (decKey k xs)
    | (Yes (t ** loc)) = Yes (t ** There loc)
    | (No notThere) = No (\(ty ** loc) => case loc of
                         Here => absurd (notHere Refl)
                         There later => absurd (notThere (ty ** later)))

NotKey : DecEq key => (k : key) -> (xs : Vect n (key, value)) -> Type
NotKey k xs = IsNo (decKey k xs)

notRowFromEvidence : DecEq key =>
                      {k : key} ->
                      (prf : Not (v ** Row k v xs)) -> NotKey k xs
notRowFromEvidence prf {k} {xs} with (decKey k xs)
  | (Yes y) = absurd (prf y)
  | (No contra) = SoFalse
