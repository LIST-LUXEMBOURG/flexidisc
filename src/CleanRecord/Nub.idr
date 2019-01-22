module CleanRecord.Nub

import CleanRecord.Row
import CleanRecord.IsNo

import Data.Vect

||| Proof that all rowents in a vector are distincts
public export
data IsNub : Vect n (a, b) -> Type where
  Nil : IsNub []
  (::) : DecEq key =>
         {k : key} -> NotLabel k xs -> IsNub xs -> IsNub ((k, v)::xs)

||| Decide whether a list is made of different rowents or not
public export
decNub : DecEq key => (xs : Vect n (key, value)) -> Dec (IsNub xs)
decNub [] = Yes []
decNub ((k,v) :: xs) with (decNub xs)
  | (Yes prf) with (decLabel k xs)
    | (Yes y)     = No (\(p :: _) => getContra p y)
    | (No contra) = Yes (notLabelFromEvidence contra :: prf)
  | (No contra) = No (\(_ :: prf) => contra prf)

public export
mapRowOnUpdate : DecEq key =>
                  {k : key} ->
                  (Label k (updateLabel xs p new)) ->
                  (Label k xs)
mapRowOnUpdate _           {p = Here} {xs = []} impossible
mapRowOnUpdate _           {p = (There _)} {xs = []} impossible
mapRowOnUpdate Here {p = Here} {xs = (k, old) :: xs} = Here
mapRowOnUpdate (There later) {p = Here} {xs = (k, old) :: xs} = There later
mapRowOnUpdate Here {p = (There later)} {xs = (x, y) :: xs} = Here
mapRowOnUpdate (There e) {p = (There later)} {xs = x :: xs} = There (mapRowOnUpdate e)

public export
updatePreservesNotField : DecEq key =>
                          {x : key} -> (p : NotLabel x xs) ->
                          NotLabel x (updateLabel xs e new)
updatePreservesNotField p = notLabelFromEvidence (getContra p . mapRowOnUpdate)

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



