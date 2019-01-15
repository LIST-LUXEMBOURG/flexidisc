module CleanRecord.Elem

import Data.Vect

import CleanRecord.IsNo

%default total

||| Proof that a key value pair is part of a vector
public export
data Elem : (k : key) -> (v : value) -> Vect n (key, value) -> Type where
  Here : Elem k v ((k, v) :: xs)
  There : (later : Elem k v xs) -> Elem k v (x::xs)

%name Elem.Elem loc, prf, e, elem

public export
Uninhabited (Elem k v []) where
  uninhabited Here impossible
  uninhabited (There _) impossible

||| Given a proof that an element is in a vector, remove it
public export
dropElem : (xs : Vect (S n) (key, value)) -> (loc : Elem k v xs) ->
           Vect n (key, value)
dropElem (_ :: xs) Here = xs
dropElem {n = S n} (x :: xs) (There later) = x :: dropElem xs later

||| Remove an element by its key, given a proof that the key is in the vector
public export
dropKey : (k : key) -> (xs : Vect (S n) (key, value)) ->
          {auto loc : Elem k v xs} ->
          Vect n (key, value)
dropKey k xs {loc} = dropElem xs loc

||| Update a value in the list given it's location and an update function
public export
updateElem : (xs : Vect n (key, value)) -> (loc : Elem k old xs) ->
             (new : value) -> Vect n (key, value)
updateElem ((x, old) :: xs) Here new = (x, new) :: xs
updateElem (x :: xs) (There later) new = x :: updateElem xs later new

||| Update a value by its key, given a proof that the key is in the vector and
||| an update function
public export
updateKey : (k : key) -> (xs : Vect n (key, value)) ->
            (f : value) ->
            {auto loc : Elem k v xs} ->
            Vect n (key, value)
updateKey k xs new {loc} = updateElem xs loc new


||| Given a proof that an element is in a list with one element dropped
||| find its location in the original list.
public export
elemFromDrop : {xs : Vect (S n) (key, value)} -> {loc : Elem k' v' xs} ->
               Elem k v (dropElem xs loc) -> Elem k v xs
elemFromDrop prf         {loc = Here}          = There prf
elemFromDrop Here        {loc = (There later)} = Here
elemFromDrop (There loc) {loc = (There later)} = There (elemFromDrop loc)

||| Decide whether a key is in a vector or not
public export
decKey : DecEq key =>
         (k : key) -> (xs : Vect n (key, value)) ->
         Dec (v ** Elem k v xs)
decKey _   [] = No (\pf => absurd (snd pf))
decKey k ((k', v') :: xs) with (decEq k k')
  | (Yes prf) = rewrite prf in Yes (v' ** Here)
  | (No notHere) with (decKey k xs)
    | (Yes (t ** loc)) = Yes (t ** There loc)
    | (No notThere) = No (\(ty ** loc) => case loc of
                         Here => absurd (notHere Refl)
                         There later => absurd (notThere (ty ** later)))

public export
NotKey : DecEq key => (k : key) -> (xs : Vect n (key, value)) -> Type
NotKey k xs = IsNo (decKey k xs)

public export
notElemFromEvidence : DecEq key =>
                      {k : key} ->
                      (prf : Not (v ** Elem k v xs)) -> NotKey k xs
notElemFromEvidence prf {k} {xs} with (decKey k xs)
  | (Yes y) = absurd (prf y)
  | (No contra) = SoFalse
