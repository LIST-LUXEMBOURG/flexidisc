module CleanRecord.Relation.Disjoint

import CleanRecord.Elem.Label
import CleanRecord.IsNo
import CleanRecord.Nub

%default total
%access public export

notThereToo : Not (Label k (x::xs)) -> Not (Label k xs)
notThereToo contra loc = contra (There loc)

notInAny : (xContra : Not (Label k xs)) ->
           (yContra : Not (Label k ys)) ->
           (Label k (xs ++ ys)) -> Void
notInAny xContra yContra pf {xs = []} =
  yContra pf
notInAny xContra yContra Here {xs = ((kx, vx) :: xs)} =
  xContra Here
notInAny xContra yContra (There later) {xs = ((kx, vx) :: xs')} =
  notInAny (notThereToo xContra) yContra later

data Disjoint : (left  : List (key, value)) ->
                (right : List (key, value)) ->
                Type where
  Nil : Disjoint [] right
  (::) : DecEq key => {k : key} ->
             NotLabel k right -> Disjoint left right ->
             Disjoint ((k,v) :: left) right

disjointNub : DecEq key =>
              (left  : List (key, value)) -> IsNub left  ->
              (right : List (key, value)) -> IsNub right ->
              Disjoint left right ->
              IsNub (left ++ right)
disjointNub [] _ _ nubRight _ = nubRight
disjointNub ((k, v) :: left) (prf :: nubLeft) right nubRight (disKV :: disjoint)
  =  notLabelFromEvidence (notInAny (getContra prf) (getContra disKV))
  :: disjointNub left nubLeft right nubRight disjoint

disjointDropLeft : (left : List (key, value)) ->
                   (right : List (key, value)) ->
                   (loc : Label k left) ->
                   Disjoint left right ->
                   Disjoint (dropLabel left loc) right
disjointDropLeft ((k, v) :: xs) right Here (_::dis) = dis
disjointDropLeft ((k, v) :: xs) right (There later) (d::dis) =
  d :: disjointDropLeft xs right later dis

relaxNotKeyContra : DecEq label =>
                    {k : label} ->
                    {loc : Label k xs} ->
                    Not (Label x xs) ->
                    Not (Label x (dropLabel xs loc))
relaxNotKeyContra contra prf = contra (labelFromDrop prf)

relaxNotKey : DecEq label =>
              (xs  : List (label, value)) ->
              (loc : Label k xs) ->
              NotLabel x xs -> NotLabel x (dropLabel xs loc)
relaxNotKey _ _ prf = notLabelFromEvidence (relaxNotKeyContra (getContra prf))

disjointDropRight : (left : List (key, value)) ->
                    (right : List (key, value)) ->
                    (loc : Label k right) ->
                    Disjoint left right ->
                    Disjoint left (dropLabel right loc)
disjointDropRight [] right loc [] = []
disjointDropRight ((kl, vl) :: left) right loc (d :: dis) =
  relaxNotKey right loc d :: disjointDropRight left right loc dis
