module CleanRecord.Nub

import CleanRecord.Row
import CleanRecord.IsNo

import Data.Vect

||| Proof that all rowents in a vector are distincts
public export
data IsNub : Vect n (a, b) -> Type where
  Nil : IsNub []
  (::) : DecEq key =>
         {k : key} -> NotKey k xs -> IsNub xs -> IsNub ((k, v)::xs)

||| Decide whether a list is made of different rowents or not
public export
decNub : DecEq key => (xs : Vect n (key, value)) -> Dec (IsNub xs)
decNub [] = Yes []
decNub ((k,v) :: xs) with (decNub xs)
  | (Yes prf) with (decKey k xs)
    | (Yes y)     = No (\(p :: _) => getContra p y)
    | (No contra) = Yes (notRowFromEvidence contra :: prf)
  | (No contra) = No (\(_ :: prf) => contra prf)

public export
mapRowOnUpdate : DecEq key =>
                  {k : key} ->
                  (v ** Row k v (updateRow xs p new)) ->
                  (v' ** Row k v' xs)
mapRowOnUpdate _           {p = Here} {xs = []} impossible
mapRowOnUpdate _           {p = (There _)} {xs = []} impossible
mapRowOnUpdate (v ** Here) {p = Here} {xs = (k, old) :: xs} = (old ** Here)
mapRowOnUpdate (v ** There later) {p = Here} {xs = (k, old) :: xs} = (v ** There later)
mapRowOnUpdate (y ** Here) {p = (There later)} {xs = (x, y) :: xs} = (y ** Here)
mapRowOnUpdate (y ** There e) {p = (There later)} {xs = x :: xs} with (mapRowOnUpdate (y ** e))
  | (z ** pf) = (z ** There pf)

public export
mapRowOnUpdateLabel : DecEq key =>
                  {k : key} ->
                  (v ** Row k v (updateLabel xs p new)) ->
                  (v' ** Row k v' xs)
mapRowOnUpdateLabel _           {p = Here} {xs = []} impossible
mapRowOnUpdateLabel _           {p = (There _)} {xs = []} impossible
mapRowOnUpdateLabel (v ** Here) {p = Here} {xs = (k, old) :: xs} = (old ** Here)
mapRowOnUpdateLabel (v ** There later) {p = Here} {xs = (k, old) :: xs} = (v ** There later)
mapRowOnUpdateLabel (y ** Here) {p = (There later)} {xs = (x, y) :: xs} = (y ** Here)
mapRowOnUpdateLabel (y ** There e) {p = (There later)} {xs = x :: xs} with (mapRowOnUpdateLabel (y ** e))
  | (z ** pf) = (z ** There pf)

public export
updatePreservesNotField : DecEq key =>
                          {x : key} -> (p : NotKey x xs) ->
                          NotKey x (updateRow xs e new)
updatePreservesNotField p = notRowFromEvidence (getContra p . mapRowOnUpdate)

public export
updateLabelPreservesNotField : DecEq key =>
                          {x : key} -> (p : NotKey x xs) ->
                          NotKey x (updateLabel xs e new)
updateLabelPreservesNotField p = notRowFromEvidence (getContra p . mapRowOnUpdateLabel)

public export
updatePreservesNub : IsNub xs -> IsNub (updateRow xs loc new)
updatePreservesNub [] {loc} = absurd loc
updatePreservesNub (p :: pf) {loc = Here} = p :: pf
updatePreservesNub (p :: pf) {loc = (There later)} = updateLabelPreservesNotField p :: updatePreservesNub pf

public export
updateLabelPreservesNub : IsNub xs -> IsNub (updateLabel xs loc new)
updateLabelPreservesNub [] {loc} = absurd loc
updateLabelPreservesNub (p :: pf) {loc = Here} = p :: pf
updateLabelPreservesNub (p :: pf) {loc = (There later)} = updateLabelPreservesNotField p :: updateLabelPreservesNub pf

public export
removeFromNubIsNotThere : DecEq key =>
                          {k : key} ->
                          IsNub xs -> (ePre : Row k v xs) -> Not (v' ** Row k v' (dropRow xs ePre))
removeFromNubIsNotThere (p :: _) Here next = absurd (getContra p next)
removeFromNubIsNotThere (p :: prf) (There later) (_ ** Here) {v} = absurd (getContra p (v ** later))
removeFromNubIsNotThere (p :: prf) (There later) (x ** There loc) = removeFromNubIsNotThere prf later (x ** loc)



