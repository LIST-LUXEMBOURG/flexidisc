module CleanRecord.OrdSub

import CleanRecord.Elem
import CleanRecord.IsNo
import CleanRecord.Nub
import Data.Vect

%default total

||| Proof that a vector is a subset of another one,
||| preserving the order of the elements
public export
data OrdSub : (xs : Vect n a) -> (ys : Vect m a) -> Type where
  Empty : OrdSub [] []
  Skip  : OrdSub xs ys -> OrdSub xs (y::ys)
  Keep  : OrdSub xs ys -> OrdSub (x::xs) (x::ys)

public export
ordSubEmpty' : (xs : Vect n a) -> OrdSub [] xs
ordSubEmpty' [] = Empty
ordSubEmpty' (_ :: xs) = Skip (ordSubEmpty' xs)

public export
ordSubEmpty : OrdSub [] xs
ordSubEmpty {xs} = ordSubEmpty' xs

public export
ordSubRefl' : (xs : Vect n a) -> OrdSub xs xs
ordSubRefl' [] = Empty
ordSubRefl' (x :: xs) = Keep (ordSubRefl' xs)

public export
ordSubRefl : OrdSub xs xs
ordSubRefl {xs} = ordSubRefl' xs

public export
elemFromOrdSub : OrdSub xs ys -> Elem x ty xs -> Elem x ty ys
elemFromOrdSub (Keep _)   Here          = Here
elemFromOrdSub (Keep ord) (There later) = There (elemFromOrdSub ord later)
elemFromOrdSub (Skip ord) loc           = There (elemFromOrdSub ord loc)

public export
notInOrdSub : DecEq key =>
              {k : key} -> OrdSub ys xs -> Not (v ** Elem k v xs) ->
              IsNo (decKey k ys)
notInOrdSub sub contra {k} {ys} with (decKey k ys)
  | (Yes (t ** loc)) = absurd (contra (t ** elemFromOrdSub sub loc))
  | (No f) = SoFalse

public export
ordSubFromDrop : (xs : Vect (S n) (key, value)) -> (loc : Elem k v xs) -> OrdSub (dropElem xs loc) xs
ordSubFromDrop ((k, v) :: ys) Here = Skip ordSubRefl
ordSubFromDrop {n = S n} (_ :: ys) (There later) = Keep (ordSubFromDrop ys later)

public export
isNubFromOrdSub : OrdSub xs ys -> IsNub ys -> IsNub xs
isNubFromOrdSub Empty [] = []
isNubFromOrdSub (Skip x) (p :: pf) = isNubFromOrdSub x pf
isNubFromOrdSub (Keep x) (p :: pf) = notInOrdSub x (getContra p) :: isNubFromOrdSub x pf
