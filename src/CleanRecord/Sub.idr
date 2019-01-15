module CleanRecord.Sub

import CleanRecord.Elem
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
  Keep  : (e : Elem k v initial) -> Sub keep (dropElem initial e) -> Sub ((k,v)::keep) initial

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
elemFromSub : Sub xs ys -> Elem x ty xs -> Elem x ty ys
elemFromSub Empty y = y
elemFromSub (Skip z) loc = There (elemFromSub z loc)
elemFromSub (Keep e _) Here = e
elemFromSub (Keep e sub) (There later) = elemFromDrop (elemFromSub sub later)

public export
notInSub : DecEq key => {k: key} -> Sub ys xs -> Not (v ** Elem k v xs) -> IsNo (decKey k ys)
notInSub sub contra {k} {ys} with (decKey k ys)
  | (Yes (t ** loc)) = absurd (contra (t ** elemFromSub sub loc))
  | (No _) = SoFalse


public export
removeFromNubIsNotThere : DecEq key =>
                          {k : key} ->
                          IsNub xs -> (ePre : Elem k v xs) -> Not (v' ** Elem k v' (dropElem xs ePre))
removeFromNubIsNotThere (p :: _) Here next = absurd (getContra p next)
removeFromNubIsNotThere (p :: prf) (There later) (_ ** Here) {v} = absurd (getContra p (v ** later))
removeFromNubIsNotThere (p :: prf) (There later) (x ** There loc) = removeFromNubIsNotThere prf later (x ** loc)


public export
isNubFromSub : Sub xs ys -> IsNub ys -> IsNub xs
isNubFromSub Empty [] = []
isNubFromSub (Skip z) (_ :: pf) = isNubFromSub z pf
isNubFromSub (Keep e z) (p :: pf) = notInSub z (removeFromNubIsNotThere (p::pf) e) :: isNubFromSub z (isNubFromOrdSub (ordSubFromDrop _ e) (p::pf))
