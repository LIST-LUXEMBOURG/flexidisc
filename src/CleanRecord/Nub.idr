module CleanRecord.Nub

import CleanRecord.Elem
import CleanRecord.IsNo

import Data.Vect

||| Proof that all elements in a vector are distincts
public export
data IsNub : Vect n (a, b) -> Type where
  Nil : IsNub []
  (::) : DecEq key =>
         {k : key} -> IsNo (decKey k xs) -> IsNub xs -> IsNub ((k, v)::xs)

||| Decide whether a list is made of different elements or not
public export
decNub : DecEq key => (xs : Vect n (key, value)) -> Dec (IsNub xs)
decNub [] = Yes []
decNub ((k,v) :: xs) with (decNub xs)
  | (Yes prf) with (decKey k xs)
    | (Yes y)     = No (\(p :: _) => getContra p y)
    | (No contra) = Yes (notElemFromEvidence contra :: prf)
  | (No contra) = No (\(_ :: prf) => contra prf)

public export
mapElemOnUpdate : DecEq key =>
                  {k : key} ->
                  (v ** Elem k v (updateElem xs p new)) ->
                  (v' ** Elem k v' xs)
mapElemOnUpdate _           {p = Here} {xs = []} impossible
mapElemOnUpdate _           {p = (There _)} {xs = []} impossible
mapElemOnUpdate (v ** Here) {p = Here} {xs = (k, old) :: xs} = (old ** Here)
mapElemOnUpdate (v ** There later) {p = Here} {xs = (k, old) :: xs} = (v ** There later)
mapElemOnUpdate (y ** Here) {p = (There later)} {xs = (x, y) :: xs} = (y ** Here)
mapElemOnUpdate (y ** There e) {p = (There later)} {xs = x :: xs} with (mapElemOnUpdate (y ** e))
  | (z ** pf) = (z ** There pf)

public export
updatePreservesNotField : DecEq key =>
                          {x : key} -> (p : IsNo (decKey x xs)) ->
                          IsNo (decKey x (updateElem xs e new))
updatePreservesNotField p = notElemFromEvidence (getContra p . mapElemOnUpdate)

public export
updatePreservesNub : IsNub xs -> IsNub (updateElem xs loc new)
updatePreservesNub [] {loc} = absurd loc
updatePreservesNub (p :: pf) {loc = Here} = p :: pf
updatePreservesNub (p :: pf) {loc = (There later)} = updatePreservesNotField p :: updatePreservesNub pf
