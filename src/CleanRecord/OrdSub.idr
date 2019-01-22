module CleanRecord.OrdSub

import CleanRecord.Label
import CleanRecord.IsNo
import CleanRecord.Nub
import Data.Vect

%default total

||| Proof that a vector is a subset of another one,
||| preserving the order of the labelents
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
labelFromOrdSub : OrdSub xs ys -> Label x xs -> Label x ys
labelFromOrdSub (Keep _)   Here          = Here
labelFromOrdSub (Keep ord) (There later) = There (labelFromOrdSub ord later)
labelFromOrdSub (Skip ord) loc           = There (labelFromOrdSub ord loc)

public export
notInOrdSub : DecEq key =>
              {k : key} -> OrdSub ys xs -> Not (Label k xs) ->
              NotLabel k ys
notInOrdSub sub contra {k} {ys} with (decLabel k ys)
  | (Yes loc) = absurd (contra (labelFromOrdSub sub loc))
  | (No f) = SoFalse

public export
ordSubFromDrop : (xs : Vect (S n) (key, value)) -> (loc : Label k xs) -> OrdSub (dropLabel xs loc) xs
ordSubFromDrop ((k, v) :: ys) Here = Skip ordSubRefl
ordSubFromDrop {n = S n} (_ :: ys) (There later) = Keep (ordSubFromDrop ys later)

public export
isNubFromOrdSub : OrdSub xs ys -> IsNub ys -> IsNub xs
isNubFromOrdSub Empty [] = []
isNubFromOrdSub (Skip x) (p :: pf) = isNubFromOrdSub x pf
isNubFromOrdSub (Keep x) (p :: pf) = notInOrdSub x (getContra p) :: isNubFromOrdSub x pf
