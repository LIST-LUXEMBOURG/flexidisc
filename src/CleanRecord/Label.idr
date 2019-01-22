module CleanRecord.Label

import Data.Vect

import CleanRecord.IsNo

%default total
%access public export

||| Proof that a key value pair is part of a vector
data Label : (k : key) -> Vect n (key, value) -> Type where
  Here : Label k ((k, v) :: xs)
  There : (later : Label k xs) -> Label k (x::xs)

%name Label lbl, loc, prf, e, elem

labelFromElem : Elem (k, v) xs -> Label k xs
labelFromElem Here = Here
labelFromElem (There later) = There (labelFromElem later)

Uninhabited (Label k []) where
  uninhabited Here impossible
  uninhabited (There _) impossible

||| Given a proof that an element is in a vector, remove it
dropLabel : (xs : Vect (S n) (key, value)) -> (loc : Label k xs) ->
           Vect n (key, value)
dropLabel (_ :: xs) Here = xs
dropLabel {n = S n} (x :: xs) (There later) = x :: dropLabel xs later

||| Remove an element by its key, given a proof that the key is in the vector
dropByKey : (k : key) -> (xs : Vect (S n) (key, value)) ->
          {auto loc : Label k xs} ->
          Vect n (key, value)
dropByKey k xs {loc} = dropLabel xs loc

||| Update a value in the list given it's location and an update function
updateLabel : (xs : Vect n (key, value)) -> (loc : Label k xs) ->
             (new : value) -> Vect n (key, value)
updateLabel ((x, old) :: xs) Here new = (x, new) :: xs
updateLabel (x :: xs) (There later) new = x :: updateLabel xs later new

||| Update a value by its key, given a proof that the key is in the vector and
||| an update function
updateKey : (k : key) -> (xs : Vect n (key, value)) ->
            (new : value) ->
            {auto loc : Label k xs} ->
            Vect n (key, value)
updateKey k xs new {loc} = updateLabel xs loc new


||| Given a proof that an element is in a list with one element dropped
||| find its location in the original list.
labelFromDrop : {xs : Vect (S n) (key, value)} -> {loc : Label k' xs} ->
               Label k (dropLabel xs loc) -> Label k xs
labelFromDrop prf         {loc = Here}          = There prf
labelFromDrop Here        {loc = (There later)} = Here
labelFromDrop (There loc) {loc = (There later)} = There (labelFromDrop loc)

||| Given a proof that an element is in a list
||| find its location in a list after one update.
labelAfterUpdate : {xs : Vect n (key, value)} ->
                   (loc : Label k xs) -> (updLoc : Label k' xs) ->
                   Label k (updateLabel xs updLoc new)
labelAfterUpdate Here Here = Here
labelAfterUpdate Here (There later) = Here
labelAfterUpdate (There later) Here = There later
labelAfterUpdate (There later) (There lbl) = There (labelAfterUpdate later lbl)

||| Decide whether a key is in a vector or not
decLabel : DecEq key =>
           (k : key) -> (xs : Vect n (key, value)) ->
           Dec (Label k xs)
decLabel _   [] = No (\pf => absurd pf)
decLabel k ((k', v') :: xs) with (decEq k k')
  | (Yes prf) = rewrite prf in Yes Here
  | (No notHere) with (decLabel k xs)
    | (Yes loc) = Yes (There loc)
    | (No notThere) = No (\loc => case loc of
                         Here => absurd (notHere Refl)
                         There later => absurd (notThere later))

NotLabel : DecEq key => (k : key) -> (xs : Vect n (key, value)) -> Type
NotLabel k xs = IsNo (decLabel k xs)

notLabelFromEvidence : DecEq key =>
                      {k : key} ->
                      (prf : Not (Label k xs)) -> NotLabel k xs
notLabelFromEvidence prf {k} {xs} with (decLabel k xs)
  | (Yes y) = absurd (prf y)
  | (No contra) = SoFalse
