module Flexidisc.OrdList.Disjoint

import Flexidisc.Dec.IsYes
import Flexidisc.OrdList.Fresh
import Flexidisc.OrdList.Label
import Flexidisc.OrdList.Nub
import Flexidisc.OrdList.Type

%default total
%access public export

||| A proof that two `OrdList` don't share a key.
data Disjoint : (left : OrdList k v o) -> (right : OrdList k v o) -> Type where
  ||| The empty `OrdList` is always `Disjoint` from another `OrdList`
  Nil : Disjoint [] right
  ||| A key in the first `OrdList` is fresh in the second `OrdList`.
  (::) : DecEq l => {k : l} -> IsFresh k right -> Disjoint left right ->
                    Disjoint ((k,v) :: left) right

%name Disjoint djt, dis, prf

freshInMerge : Fresh l left -> Fresh l right -> Fresh l (merge left right)
freshInMerge [] freshR = freshR
freshInMerge (f :: fresh) [] = f :: fresh
freshInMerge (f :: fresh) (g :: prf)
  {left = ((ll, tl) :: xs)} {right = ((lr, tr) :: hs)} with (ll < lr)
  | True  = f :: freshInMerge fresh (g :: prf)
  | False = g :: freshInMerge (f :: fresh) prf

invertFresh : Disjoint left ((lr, ty)::right) -> Fresh lr left
invertFresh [] = []
invertFresh (fresh :: djt) =
  (\(f :: _) => f . sym) (getProof fresh) :: invertFresh djt

disjointSmallerRight : Disjoint left (r::right) -> Disjoint left right
disjointSmallerRight [] = []
disjointSmallerRight (fresh :: djt) =
  tailIsFresh fresh :: disjointSmallerRight djt

disjointNub : Disjoint left right -> Nub left -> Nub right ->
              Nub (merge left right)
disjointNub djt [] z = z
disjointNub djt (yes :: x) [] = yes :: x
disjointNub (fll :: djt) (yes :: x) (prf :: w)
  {left = ((ll, tl) :: xs)} {right = ((lr, tr) :: hs)} with (ll < lr)
  | True  = freshInMerge yes (getProof fll) :: disjointNub djt x (prf :: w)
  | False = freshInMerge (invertFresh (fll :: djt)) prf
              :: disjointNub (disjointSmallerRight (fll :: djt)) (yes :: x) w
