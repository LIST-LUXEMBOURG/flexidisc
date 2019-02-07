module CleanRecord.OrdHeader.Label

import CleanRecord.OrdHeader.Type

%default total
%access public export

data OrdLabel : (k : l) -> (xs : OrdHeader l o) -> Type where
  Here : OrdLabel k ((k,v)::xs)
  There : (later : OrdLabel k xs) -> OrdLabel k (x::xs)

%name OrdLabel lbl, loc, prf, e, elem

atLabel : (xs : OrdHeader l o) -> (loc : OrdLabel k xs) -> Type
atLabel ((_, v) :: _) Here = v
atLabel (_ :: xs) (There later) = atLabel xs later

Uninhabited (OrdLabel k []) where
  uninhabited Here      impossible
  uninhabited (There _) impossible

||| Given a proof that an element is in a vector, remove it
dropLabel : (xs : OrdHeader k o) -> (loc : OrdLabel l xs) -> OrdHeader k o
dropLabel (_ :: xs) Here          = xs
dropLabel (x :: xs) (There later) = x :: dropLabel xs later

||| Update a value in the list given it's location and an update function
changeType : (xs : OrdHeader k o) -> (loc : OrdLabel l xs) ->
             (new : Type) -> OrdHeader k o
changeType ((x, old) :: xs) Here          new = (x, new) :: xs
changeType (x :: xs)        (There later) new = x :: changeType xs later new
