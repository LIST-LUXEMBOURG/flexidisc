module CleanRecord.OrdHeader.Disjoint

import CleanRecord.Dec.IsYes
import CleanRecord.OrdHeader.Fresh
import CleanRecord.OrdHeader.Label
import CleanRecord.OrdHeader.Nub
import CleanRecord.OrdHeader.Type

%default total
%access public export

data Disjoint : (left : OrdHeader k o) -> (right : OrdHeader k o2) -> Type where
  Nil : Disjoint [] right
  (::) : DecEq l => {k : l} -> IsFresh k right -> Disjoint left right ->
                    Disjoint ((k,v) :: left) right

%name Disjoint djt, dis, prf

freshTail : DecEq k => {l : k} -> IsFresh l (x::xs) -> IsFresh l xs
freshTail = isFreshFromEvidence . (\ (_::fresh) => fresh) . getProof

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
  (\(f :: _) => f . sym) (getProof fresh)
  :: invertFresh djt

disjointSmallerRight : Disjoint left (r::right) -> Disjoint left right
disjointSmallerRight [] = []
disjointSmallerRight (fresh :: djt) =
  freshTail fresh :: disjointSmallerRight djt

disjointNub : Disjoint left right -> Nub left -> Nub right ->
              Nub (merge left right)
disjointNub djt [] z {left = []} {right = right} = z
disjointNub djt (yes :: x) [] {left = ((l, ty) :: xs)} {right = []} = yes :: x
disjointNub (fll :: djt) (yes :: x) (prf :: w)
            {left = ((ll, tl) :: xs)} {right = ((lr, tr) :: hs)} with (ll < lr)
  | True  = freshInMerge yes (getProof fll)
              :: disjointNub djt x (prf :: w)
  | False = freshInMerge (invertFresh (fll :: djt)) prf
              :: disjointNub (disjointSmallerRight (fll :: djt)) (yes :: x) w
