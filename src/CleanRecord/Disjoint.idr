module CleanRecord.Disjoint

import CleanRecord.Elem
import CleanRecord.IsNo
import CleanRecord.Nub
import Data.Vect

%default total

public export
notThereToo : Not (v ** Elem k v (x::xs)) -> Not (v' ** Elem k v' xs)
notThereToo contra (v' ** loc) = contra (v' ** There loc)

public export
notInAny : (xContra : Not (vx ** Elem k vx xs)) ->
           (yContra : Not (vy ** Elem k vy ys)) ->
           (v ** Elem k v (xs ++ ys)) -> Void
notInAny xContra yContra (v ** pf) {xs = []} =
  yContra (v ** pf)
notInAny xContra yContra (vx ** Here) {xs = ((kx, vx) :: xs)} =
  xContra (vx ** Here)
notInAny xContra yContra (v ** There later) {xs = ((kx, vx) :: xs')} =
  notInAny (notThereToo xContra) yContra (v ** later)

public export
data Disjoint : (left  : Vect n (key, value)) ->
                (right : Vect m (key, value)) ->
                Type where
  Nil : Disjoint [] right
  (::) : DecEq key => {k : key} ->
             NotKey k right -> Disjoint left right ->
             Disjoint ((k,v) :: left) right

public export
disjointNub : DecEq key =>
              (left  : Vect n (key, value)) -> IsNub left  ->
              (right : Vect m (key, value)) -> IsNub right ->
              Disjoint left right ->
              IsNub (left ++ right)
disjointNub [] _ _ nubRight _ = nubRight
disjointNub ((k, v) :: left) (prf :: nubLeft) right nubRight (disKV :: disjoint)
  =  notElemFromEvidence (notInAny (getContra prf) (getContra disKV))
  :: disjointNub left nubLeft right nubRight disjoint

public export
disjointDropLeft : (left : Vect (S n) (key, value)) ->
                   (right : Vect m (key, value)) ->
                   (loc : Elem k v left) ->
                   Disjoint left right ->
                   Disjoint (dropElem left loc) right
disjointDropLeft ((k, v) :: xs) right Here (_::dis) = dis
disjointDropLeft {n = S n} ((k, v) :: xs) right (There later) (d::dis) =
  d :: disjointDropLeft xs right later dis

public export
relaxNotKeyContra : DecEq label =>
                    {k : label} ->
                    {loc : Elem k _ xs} ->
                    Not (v ** Elem x v xs) ->
                    Not (v ** Elem x v (dropElem xs loc))
relaxNotKeyContra contra (v ** prf) = contra (v ** elemFromDrop prf)

public export
relaxNotKey : DecEq label =>
              (xs  : Vect (S n) (label, value)) ->
              (loc : Elem k ty xs) ->
              NotKey x xs -> NotKey x (dropElem xs loc)
relaxNotKey _ _ prf = notElemFromEvidence (relaxNotKeyContra (getContra prf))

public export
disjointDropRight : (left : Vect n (key, value)) ->
                    (right : Vect (S m) (key, value)) ->
                    (loc : Elem k v right) ->
                    Disjoint left right ->
                    Disjoint left (dropElem right loc)
disjointDropRight [] right loc [] = []
disjointDropRight ((kl, vl) :: left) right loc (d :: dis) =
  relaxNotKey right loc d :: disjointDropRight left right loc dis
