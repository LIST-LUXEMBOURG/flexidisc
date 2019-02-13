module CleanRecord.OrdList.Label

import CleanRecord.OrdList.Type

%default total
%access public export

data OrdLabel : (l : k) -> (xs : OrdList k v o) -> Type where
  Here : OrdLabel l ((l,v)::xs)
  There : (later : OrdLabel l xs) -> OrdLabel l (x::xs)

%name OrdLabel lbl, loc, prf, e, elem

atLabel : (xs : OrdList l v o) -> (loc : OrdLabel k xs) -> v
atLabel ((_, v) :: _) Here = v
atLabel (_ :: xs) (There later) = atLabel xs later

Uninhabited (OrdLabel k []) where
  uninhabited Here      impossible
  uninhabited (There _) impossible

decLabel : DecEq k => (l : k) -> (xs : OrdList k v o) -> Dec (OrdLabel l xs)
decLabel l [] = No uninhabited
decLabel l ((kx, vx) :: xs) with (decEq l kx)
  | (Yes prf) = Yes (rewrite prf in Here)
  | (No contraHere) with (decLabel l xs)
    | (Yes prf) = Yes (There prf)
    | (No contraThere) = No (\p => case p of
                                        Here => contraHere Refl
                                        There later => contraThere later)

||| Given a proof that an element is in a vector, remove it
dropLabel : (xs : OrdList k v o) -> (loc : OrdLabel l xs) -> OrdList k v o
dropLabel (_ :: xs) Here          = xs
dropLabel (x :: xs) (There later) = x :: dropLabel xs later

||| Update a value in the list given it's location and an update function
changeValue : (xs : OrdList k v o) -> (loc : OrdLabel l xs) ->
             (new : v) -> OrdList k v o
changeValue ((x, old) :: xs) Here          new = (x, new) :: xs
changeValue (x :: xs)        (There later) new = x :: changeValue xs later new