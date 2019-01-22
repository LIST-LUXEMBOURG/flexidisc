module CleanRecord.Disjoint

import CleanRecord.Row
import CleanRecord.IsNo
import CleanRecord.Nub
import Data.Vect

%default total

public export
notThereToo : Not (Label k (x::xs)) -> Not (Label k xs)
notThereToo contra loc = contra (There loc)

public export
notInAny : (xContra : Not (Label k xs)) ->
           (yContra : Not (Label k ys)) ->
           (Label k (xs ++ ys)) -> Void
notInAny xContra yContra pf {xs = []} =
  yContra pf
notInAny xContra yContra Here {xs = ((kx, vx) :: xs)} =
  xContra Here
notInAny xContra yContra (There later) {xs = ((kx, vx) :: xs')} =
  notInAny (notThereToo xContra) yContra later

public export
data Disjoint : (left  : Vect n (key, value)) ->
                (right : Vect m (key, value)) ->
                Type where
  Nil : Disjoint [] right
  (::) : DecEq key => {k : key} ->
             NotLabel k right -> Disjoint left right ->
             Disjoint ((k,v) :: left) right

public export
disjointNub : DecEq key =>
              (left  : Vect n (key, value)) -> IsNub left  ->
              (right : Vect m (key, value)) -> IsNub right ->
              Disjoint left right ->
              IsNub (left ++ right)
disjointNub [] _ _ nubRight _ = nubRight
disjointNub ((k, v) :: left) (prf :: nubLeft) right nubRight (disKV :: disjoint)
  =  notLabelFromEvidence (notInAny (getContra prf) (getContra disKV))
  :: disjointNub left nubLeft right nubRight disjoint

public export
disjointDropLeft : (left : Vect (S n) (key, value)) ->
                   (right : Vect m (key, value)) ->
                   (loc : Label k left) ->
                   Disjoint left right ->
                   Disjoint (dropLabel left loc) right
disjointDropLeft ((k, v) :: xs) right Here (_::dis) = dis
disjointDropLeft {n = S n} ((k, v) :: xs) right (There later) (d::dis) =
  d :: disjointDropLeft xs right later dis

public export
relaxNotKeyContra : DecEq label =>
                    {k : label} ->
                    {loc : Label k xs} ->
                    Not (Label x xs) ->
                    Not (Label x (dropLabel xs loc))
relaxNotKeyContra contra prf = contra (labelFromDrop prf)

public export
relaxNotKey : DecEq label =>
              (xs  : Vect (S n) (label, value)) ->
              (loc : Label k xs) ->
              NotLabel x xs -> NotLabel x (dropLabel xs loc)
relaxNotKey _ _ prf = notLabelFromEvidence (relaxNotKeyContra (getContra prf))

public export
disjointDropRight : (left : Vect n (key, value)) ->
                    (right : Vect (S m) (key, value)) ->
                    (loc : Label k right) ->
                    Disjoint left right ->
                    Disjoint left (dropLabel right loc)
disjointDropRight [] right loc [] = []
disjointDropRight ((kl, vl) :: left) right loc (d :: dis) =
  relaxNotKey right loc d :: disjointDropRight left right loc dis
