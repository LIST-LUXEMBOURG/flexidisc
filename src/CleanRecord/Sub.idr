module CleanRecord.Sub

import CleanRecord.Row
import CleanRecord.IsNo
import CleanRecord.Nub
import CleanRecord.OrdSub

import Data.Vect

%default total


public export
data Sub : (sub : Vect n (key, value)) ->
           (initial : Vect m (key, value)) ->
           Type where
  Empty : Sub [] []
  Skip  : Sub sub initial -> Sub sub ((k,v) :: initial)
  Keep  : (e : Row k v initial) -> Sub keep (dropRow initial e) -> Sub ((k,v)::keep) initial

public export
subEmpty' : (xs : Vect n (key, value)) -> Sub [] xs
subEmpty' [] = Empty
subEmpty' ((k, v) :: xs) = Skip (subEmpty' xs)

public export
subEmpty : Sub [] xs
subEmpty {xs} = subEmpty' xs

public export
subRefl' : (xs : Vect n (key, value)) -> Sub xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep Here (subRefl' xs)

public export
subRefl : Sub xs xs
subRefl {xs} = subRefl' xs


public export
rowFromSub : Sub xs ys -> Row x ty xs -> Row x ty ys
rowFromSub Empty y = y
rowFromSub (Skip z) loc = There (rowFromSub z loc)
rowFromSub (Keep e _) Here = e
rowFromSub (Keep e sub) (There later) = rowFromDrop (rowFromSub sub later)

public export
notInSub : DecEq key =>
           {k: key} -> Sub ys xs -> Not (v ** Row k v xs) -> NotKey k ys
notInSub sub contra {k} {ys} with (decKey k ys)
  | (Yes (t ** loc)) = absurd (contra (t ** rowFromSub sub loc))
  | (No _) = SoFalse


public export
isNubFromSub : Sub xs ys -> IsNub ys -> IsNub xs
isNubFromSub Empty [] = []
isNubFromSub (Skip z) (_ :: pf) = isNubFromSub z pf
isNubFromSub (Keep e z) (p :: pf) =
  notInSub z (removeFromNubIsNotThere (p::pf) e) ::
  isNubFromSub z (isNubFromOrdSub (ordSubFromDrop _ (labelFromRow e)) (p::pf))
