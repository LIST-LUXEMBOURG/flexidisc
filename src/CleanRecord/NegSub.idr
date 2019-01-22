module CleanRecord.NegSub

import CleanRecord.Label
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
  Skip  : (e : Label k initial) -> NegSub keep (dropLabel initial e) -> NegSub keep initial
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
shiftLabel :  (loc : Label k ys) -> Label x (dropLabel ys loc) -> Label x ys
shiftLabel Here label = There label
shiftLabel (There later) Here = Here
shiftLabel (There later) (There label) = There (shiftLabel later label)

public export
labelFromNegSub : NegSub xs ys -> Label x xs -> Label x ys
labelFromNegSub Empty label = label
labelFromNegSub (Skip loc sub) label = shiftLabel loc (labelFromNegSub sub label)
labelFromNegSub (Keep x) Here = Here
labelFromNegSub (Keep sub) (There later) = There (labelFromNegSub sub later)


public export
notInNegSub : DecEq key =>
              {k: key} -> NegSub ys xs -> Not (Label k xs) -> NotLabel k ys
notInNegSub sub contra {k} {ys} with (decLabel k ys)
  | (Yes loc) = absurd (contra (labelFromNegSub sub loc))
  | (No _) = SoFalse


public export
isNubFromNegSub : NegSub xs ys -> IsNub ys -> IsNub xs
isNubFromNegSub Empty nub = nub
isNubFromNegSub (Skip e x) pf = isNubFromNegSub x (isNubFromOrdSub (ordSubFromDrop _ e) pf)
isNubFromNegSub (Keep x) (p :: pf) = notInNegSub x (getContra p) :: isNubFromNegSub x pf
