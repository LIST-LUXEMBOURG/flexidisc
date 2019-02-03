module CleanRecord.Label

import CleanRecord.IsNo

import Data.List

%default total
%access public export

||| Proof that a key value pair is part of a vector
data Label : (k : key) -> List (key, value) -> Type where
  Here  :                         Label k ((k, v) :: xs)
  There : (later : Label k xs) -> Label k (x      :: xs)

%name Label lbl, loc, prf, e, elem

labelFromElem : Elem (k, v) xs -> Label k xs
labelFromElem Here          = Here
labelFromElem (There later) = There (labelFromElem later)

Uninhabited (Label k []) where
  uninhabited Here      impossible
  uninhabited (There _) impossible

||| Given a proof that an element is in a vector, remove it
dropLabel : (xs : List (key, value)) -> (loc : Label k xs) ->
            List (key, value)
dropLabel (_ :: xs) Here          = xs
dropLabel (x :: xs) (There later) = x :: dropLabel xs later

||| Update a value in the list given it's location and an update function
changeLabel : (xs : List (key, value)) -> (loc : Label old xs) ->
              (new : key) -> List (key, value)
changeLabel ((old, v) :: xs) Here          new = (new, v) :: xs
changeLabel (x :: xs)        (There later) new = x :: changeLabel xs later new

||| Update a value in the list given it's location and an update function
updateLabel : (xs : List (key, value)) -> (loc : Label k xs) ->
              (new : value) -> List (key, value)
updateLabel ((x, old) :: xs) Here          new = (x, new) :: xs
updateLabel (x :: xs)        (There later) new = x :: updateLabel xs later new

||| Given a proof that an element is in a list with one element dropped
||| find its location in the original list.
labelFromDrop : {xs : List (key, value)} -> {loc : Label k' xs} ->
                Label k (dropLabel xs loc) -> Label k xs
labelFromDrop prf         {loc = Here}          = There prf
labelFromDrop Here        {loc = (There later)} = Here
labelFromDrop (There loc) {loc = (There later)} = There (labelFromDrop loc)

||| Given a proof that an element is in a list
||| find its location in a list after one update.
labelAfterUpdate : {xs : List (key, value)} ->
                   (loc : Label k xs) -> (updLoc : Label k' xs) ->
                   Label k (updateLabel xs updLoc new)
labelAfterUpdate Here          Here        = Here
labelAfterUpdate Here          (There _)   = Here
labelAfterUpdate (There later) Here        = There later
labelAfterUpdate (There later) (There lbl) = There (labelAfterUpdate later lbl)

||| Decide whether a key is in a vector or not
decLabel : DecEq key =>
           (k : key) -> (xs : List (key, value)) ->
           Dec (Label k xs)
decLabel _   [] = No (\pf => absurd pf)
decLabel k ((k', v') :: xs) with (decEq k k')
  | (Yes prf) = rewrite prf in Yes Here
  | (No notHere) with (decLabel k xs)
    | (Yes loc)     = Yes (There loc)
    | (No notThere) = No (\loc => case loc of
                                       Here        => absurd (notHere Refl)
                                       There later => absurd (notThere later))

NotLabel : DecEq key => (k : key) -> (xs : List (key, value)) -> Type
NotLabel k xs = IsNo (decLabel k xs)

%hint
notLabelFromEvidence : DecEq key =>
                       {k : key} ->
                       (prf : Not (Label k xs)) -> NotLabel k xs
notLabelFromEvidence prf {k} {xs} with (decLabel k xs)
  | (Yes y) = absurd (prf y)
  | (No contra) = SoFalse
