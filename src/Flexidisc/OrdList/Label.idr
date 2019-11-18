module Flexidisc.OrdList.Label

import Flexidisc.OrdList.Type

%default total
%access public export

||| Proof that a label is in an `OrdList`
data OrdLabel : (l : k) -> (xs : OrdList k o v) -> Type where
  ||| The label is in the first element of the list
  Here : OrdLabel l ((l,v)::xs)
  ||| The label is in the tail
  There : (later : OrdLabel l xs) -> OrdLabel l (x::xs)

%name OrdLabel lbl, loc, prf, e, elem

||| Given a proof that a label is in the list, get the corresponding value back
atLabel : (xs : OrdList k o v) -> (loc : OrdLabel l xs) -> v
atLabel ((_, v) :: _) Here = v
atLabel (_ :: xs) (There later) = atLabel xs later

Uninhabited (OrdLabel k []) where
  uninhabited Here      impossible
  uninhabited (There _) impossible

||| Decide whether a label is in a list or not
decLabel : DecEq k => (l : k) -> (xs : OrdList k o v) -> Dec (OrdLabel l xs)
decLabel l [] = No uninhabited
decLabel l ((kx, vx) :: xs) with (decEq l kx)
  | (Yes prf) = Yes (rewrite prf in Here)
  | (No contraHere) with (decLabel l xs)
    | (Yes prf) = Yes (There prf)
    | (No contraThere) = No (\p => case p of
                                        Here => contraHere Refl
                                        There later => contraThere later)

||| Given a proof that an element is in a vector, remove it
dropLabel : (xs : OrdList k o v) -> (loc : OrdLabel l xs) -> OrdList k o v
dropLabel (_ :: xs) Here          = xs
dropLabel (x :: xs) (There later) = x :: dropLabel xs later

||| Update a value in the list given it's location and a new value
changeValue : (xs : OrdList k o v) -> (loc : OrdLabel l xs) ->
             (new : v) -> OrdList k o v
changeValue ((x, old) :: xs) Here          new = (x, new) :: xs
changeValue (x :: xs)        (There later) new = x :: changeValue xs later new
