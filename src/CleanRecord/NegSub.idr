module CleanRecord.NegSub

import CleanRecord.Row
import CleanRecord.IsNo
import CleanRecord.Nub
import CleanRecord.OrdSub

import Data.Vect

%default total


public export
data NegSub : (sub : Vect n (key, value)) ->
           (initial : Vect m (key, value)) ->
           Type where
  Empty : NegSub [] []
  Skip  : (e : Label k initial) -> NegSub keep (dropRow initial e) -> NegSub keep initial
  Keep  : NegSub sub initial -> NegSub ((k,v)::sub) ((k,v) :: initial)

public export
subEmpty' : (xs : Vect n (key, value)) -> NegSub [] xs
subEmpty' [] = Empty
subEmpty' ((k,v) :: xs) = Skip Here (subEmpty' xs)

public export
subEmpty : NegSub [] xs
subEmpty {xs} = subEmpty' xs

public export
subRefl' : (xs : Vect n (key, value)) -> NegSub xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep (subRefl' xs)

public export
subRefl : NegSub xs xs
subRefl {xs} = subRefl' xs


public export
shiftRow :  (loc : Row k v ys) -> Row x ty (dropRow ys loc) -> Row x ty ys
shiftRow Here row = There row
shiftRow (There later) Here = Here
shiftRow (There later) (There row) = There (shiftRow later row)

public export
rowFromNegSub : NegSub xs ys -> Row x ty xs -> Row x ty ys
rowFromNegSub Empty row = row
rowFromNegSub (Skip loc sub) row = shiftRow loc (rowFromNegSub sub row)
rowFromNegSub (Keep x) Here = Here
rowFromNegSub (Keep sub) (There later) = There (rowFromNegSub sub later)


public export
notInNegSub : DecEq key =>
           {k: key} -> NegSub ys xs -> Not (v ** Row k v xs) -> NotKey k ys
notInNegSub sub contra {k} {ys} with (decKey k ys)
  | (Yes (t ** loc)) = absurd (contra (t ** rowFromNegSub sub loc))
  | (No _) = SoFalse


public export
isNubFromNegSub : NegSub xs ys -> IsNub ys -> IsNub xs
isNubFromNegSub Empty nub = nub
isNubFromNegSub (Skip e x) pf = isNubFromNegSub x (isNubFromOrdSub (ordSubFromDrop _ (labelFromRow e)) pf)
isNubFromNegSub (Keep x) (p :: pf) = notInNegSub x (getContra p) :: isNubFromNegSub x pf
