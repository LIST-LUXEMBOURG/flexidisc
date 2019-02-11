module CleanRecord.OrdList.Label

import CleanRecord.OrdList.Type

%default total
%access public export

data OrdLabel : (k : l) -> (xs : OrdList l v o) -> Type where
  Here : OrdLabel k ((k,v)::xs)
  There : (later : OrdLabel k xs) -> OrdLabel k (x::xs)

%name OrdLabel lbl, loc, prf, e, elem

atLabel : (xs : OrdList l v o) -> (loc : OrdLabel k xs) -> v
atLabel ((_, v) :: _) Here = v
atLabel (_ :: xs) (There later) = atLabel xs later

Uninhabited (OrdLabel k []) where
  uninhabited Here      impossible
  uninhabited (There _) impossible

||| Given a proof that an element is in a vector, remove it
dropLabel : (xs : OrdList k v o) -> (loc : OrdLabel l xs) -> OrdList k v o
dropLabel (_ :: xs) Here          = xs
dropLabel (x :: xs) (There later) = x :: dropLabel xs later

||| Update a value in the list given it's location and an update function
changeValue : (xs : OrdList k v o) -> (loc : OrdLabel l xs) ->
             (new : v) -> OrdList k v o
changeValue ((x, old) :: xs) Here          new = (x, new) :: xs
changeValue (x :: xs)        (There later) new = x :: changeValue xs later new
