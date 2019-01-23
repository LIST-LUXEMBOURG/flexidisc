||| This module introduce the proof that a Vect is an ordered subset of
||| another one.
|||
||| It's not really useful directly, but is used internally at many places.
module CleanRecord.Relation.OrdSub

import CleanRecord.Label
import CleanRecord.IsNo
import CleanRecord.Nub
import Data.Vect

%default total
%access public export

||| Proof that a vector is a subset of another one,
||| preserving the order of the elements
data OrdSub : (xs : Vect n a) -> (ys : Vect m a) -> Type where
  Empty : OrdSub [] []
  Skip  : OrdSub xs ys -> OrdSub xs (y::ys)
  Keep  : OrdSub xs ys -> OrdSub (x::xs) (x::ys)

||| An empty `Vect` is an ordered subset of any `Any`
ordSubEmpty' : (xs : Vect n a) -> OrdSub [] xs
ordSubEmpty' [] = Empty
ordSubEmpty' (_ :: xs) = Skip (ordSubEmpty' xs)

||| An empty `Vect` is an ordered subset of any `Vect`
ordSubEmpty : OrdSub [] xs
ordSubEmpty {xs} = ordSubEmpty' xs

||| A `Vect` is an ordered subset of itself
ordSubRefl' : (xs : Vect n a) -> OrdSub xs xs
ordSubRefl' [] = Empty
ordSubRefl' (x :: xs) = Keep (ordSubRefl' xs)

||| A `Vect` is an ordered subset of itself
ordSubRefl : OrdSub xs xs
ordSubRefl {xs} = ordSubRefl' xs

||| Given the proof that a Label is in an ordered subset of a vect
||| provide a proof that this label is in the initial vect
labelFromOrdSub : OrdSub xs ys -> Label x xs -> Label x ys
labelFromOrdSub (Keep _)   Here          = Here
labelFromOrdSub (Keep ord) (There later) = There (labelFromOrdSub ord later)
labelFromOrdSub (Skip ord) loc           = There (labelFromOrdSub ord loc)

||| If a label is not in the initial vector, it can't be in an
||| ordered subset of this vect
notInOrdSub : DecEq key =>
              {k : key} -> OrdSub ys xs -> Not (Label k xs) ->
              NotLabel k ys
notInOrdSub sub contra {k} {ys} with (decLabel k ys)
  | (Yes loc) = absurd (contra (labelFromOrdSub sub loc))
  | (No f) = SoFalse

||| If we drop an element, we obtain an ordered subset of the initial vector
ordSubFromDrop : (xs : Vect (S n) (key, value)) -> (loc : Label k xs) ->
                 OrdSub (dropLabel xs loc) xs
ordSubFromDrop ((k, v) :: ys) Here = Skip ordSubRefl
ordSubFromDrop {n = S n} (_ :: ys) (There later) = Keep (ordSubFromDrop ys later)

||| If the original vector doesn't contain any duplicate,
||| an orderred subset doesn't contain duplicate as well
isNubFromOrdSub : OrdSub xs ys -> IsNub ys -> IsNub xs
isNubFromOrdSub Empty [] = []
isNubFromOrdSub (Skip x) (p :: pf) = isNubFromOrdSub x pf
isNubFromOrdSub (Keep x) (p :: pf) = notInOrdSub x (getContra p) :: isNubFromOrdSub x pf
