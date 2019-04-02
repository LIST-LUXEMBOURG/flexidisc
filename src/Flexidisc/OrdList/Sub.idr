module Flexidisc.OrdList.Sub

import Flexidisc.Dec.IsYes
import Flexidisc.OrdList.Fresh
import Flexidisc.OrdList.Label
import Flexidisc.OrdList.Nub
import Flexidisc.OrdList.Row
import Flexidisc.OrdList.Type

%default total
%access public export

||| Proof that an `OrdList` is a permutation of another vect
public export
data Sub : (xs : OrdList k v o) -> (ys : OrdList k v o) -> Type where
  Empty : Sub [] []
  Skip  : Sub xs ys -> Sub xs (y::ys)
  Keep  : Sub xs ys -> Sub (x::xs) (x::ys)

%name Sub sub, issub, ss

||| An empty `OrdList` is an ordered subset of any `Any`
subEmpty' : (xs : OrdList k v o) -> Sub [] xs
subEmpty' [] = Empty
subEmpty' (_ :: xs) = Skip (subEmpty' xs)

||| An empty `OrdList` is an ordered subset of any `OrdList`
subEmpty : Sub [] xs
subEmpty {xs} = subEmpty' xs

||| A `OrdList` is an ordered subset of itself
subRefl' : (xs : OrdList k v o) -> Sub xs xs
subRefl' [] = Empty
subRefl' (x :: xs) = Keep (subRefl' xs)

||| A `OrdList` is an ordered subset of itself
subRefl : Sub xs xs
subRefl {xs} = subRefl' xs

freshInSub : Sub xs ys -> Fresh l ys -> Fresh l xs
freshInSub Empty fresh = fresh
freshInSub (Skip sub) (f :: fresh) = freshInSub sub fresh
freshInSub (Keep sub) (f :: fresh) = f :: freshInSub sub fresh

||| If the original vector doesn't contain any duplicate,
||| an orderred subset doesn't contain duplicate as well
isNubFromSub : Sub xs ys -> Nub ys -> Nub xs
isNubFromSub Empty y = y
isNubFromSub (Skip sub) (yes :: prf) = isNubFromSub sub prf
isNubFromSub (Keep sub) (yes :: prf) =
  freshInSub sub yes :: isNubFromSub sub prf

%hint
rowFromSub : Sub xs ys -> OrdRow key ty xs -> OrdRow key ty ys
rowFromSub Empty lbl = lbl
rowFromSub (Skip sub) loc = There (rowFromSub sub loc)
rowFromSub (Keep sub) Here = Here
rowFromSub (Keep sub) (There later) = There (rowFromSub sub later)


||| Given the proof that a Label is in an subset of a vect
||| provide a proof that this label is in the initial vect
%hint
labelFromSub : Sub xs ys -> OrdLabel x xs -> OrdLabel x ys
labelFromSub Empty y = y
labelFromSub (Skip z) loc = There (labelFromSub z loc)
labelFromSub (Keep _) Here = Here
labelFromSub (Keep sub) (There later) = There (labelFromSub sub later)
