module CleanRecord.Nub

import CleanRecord.Label
import CleanRecord.IsNo

import Data.Vect

||| Proof that all labelents in a vector are distincts
public export
data IsNub : Vect n (a, b) -> Type where
  Nil : IsNub []
  (::) : DecEq key =>
         {k : key} -> NotLabel k xs -> IsNub xs -> IsNub ((k, v)::xs)

||| Decide whether a list is made of different labelents or not
public export
decNub : DecEq key => (xs : Vect n (key, value)) -> Dec (IsNub xs)
decNub [] = Yes []
decNub ((k,v) :: xs) with (decNub xs)
  | (Yes prf) with (decLabel k xs)
    | (Yes y)     = No (\(p :: _) => getContra p y)
    | (No contra) = Yes (notLabelFromEvidence contra :: prf)
  | (No contra) = No (\(_ :: prf) => contra prf)

public export
mapLabelOnUpdate : DecEq key =>
                  {k : key} ->
                  (Label k (updateLabel xs p new)) ->
                  (Label k xs)
mapLabelOnUpdate _           {p = Here} {xs = []} impossible
mapLabelOnUpdate _           {p = (There _)} {xs = []} impossible
mapLabelOnUpdate Here {p = Here} {xs = (k, old) :: xs} = Here
mapLabelOnUpdate (There later) {p = Here} {xs = (k, old) :: xs} = There later
mapLabelOnUpdate Here {p = (There later)} {xs = (x, y) :: xs} = Here
mapLabelOnUpdate (There e) {p = (There later)} {xs = x :: xs} = There (mapLabelOnUpdate e)

public export
updatePreservesNotField : DecEq key =>
                          {x : key} -> (p : NotLabel x xs) ->
                          NotLabel x (updateLabel xs e new)
updatePreservesNotField p = notLabelFromEvidence (getContra p . mapLabelOnUpdate)

public export
updatePreservesNub : IsNub xs -> IsNub (updateLabel xs loc new)
updatePreservesNub [] {loc} = absurd loc
updatePreservesNub (p :: pf) {loc = Here} = p :: pf
updatePreservesNub (p :: pf) {loc = (There later)} = updatePreservesNotField p :: updatePreservesNub pf

public export
removeFromNubIsNotThere : DecEq key =>
                          {k : key} ->
                          IsNub xs -> (ePre : Label k xs) -> Not (Label k (dropLabel xs ePre))
removeFromNubIsNotThere (p :: _) Here next = absurd (getContra p next)
removeFromNubIsNotThere (p :: prf) (There later) Here = absurd (getContra p later)
removeFromNubIsNotThere (p :: prf) (There later) (There loc) = removeFromNubIsNotThere prf later loc
