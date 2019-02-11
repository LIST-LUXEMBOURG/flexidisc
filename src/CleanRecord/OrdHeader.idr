module CleanRecord.OrdHeader

import public CleanRecord.OrdHeader.CompWithKeys
import public CleanRecord.OrdHeader.Disjoint
import public CleanRecord.OrdHeader.HereOrNot
import public CleanRecord.OrdHeader.Fresh
import public CleanRecord.OrdHeader.Label
import public CleanRecord.OrdHeader.Nub
import public CleanRecord.OrdHeader.Permute
import public CleanRecord.OrdHeader.Row
import public CleanRecord.OrdHeader.Sub
import public CleanRecord.OrdHeader.SubWithKeys
import public CleanRecord.OrdHeader.Type

%default total
%access public export

data SameOrd : (xs : OrdHeader k o) -> (ys : OrdHeader k o) -> Type where
  Same : SameOrd xs ys

diffKeys : DecEq k =>
           (xs : OrdHeader k o) -> (ys : OrdHeader k o) -> OrdHeader k o
diffKeys [] ys = []
diffKeys ((lx, vx) :: xs) ys with (decFresh lx ys)
  | (Yes prf) = (lx, vx) :: diffKeys xs ys
  | (No contra) = diffKeys xs ys

diffIsSub : DecEq k => {xs : OrdHeader k o} ->
            Sub (diffKeys xs ys) xs
diffIsSub {xs = []} = Empty
diffIsSub {xs = (lx, vx) :: xs} {ys} with (decFresh lx ys)
  | (Yes prf) = Keep diffIsSub
  | (No contra) = Skip diffIsSub

diffIsDisjoint : DecEq k => {xs : OrdHeader k o} ->
                 Disjoint (diffKeys xs ys) ys
diffIsDisjoint {xs = []} = []
diffIsDisjoint {xs = (kx, vx) :: xs} {ys} with (decFresh kx ys)
  | (Yes prf) = isFreshFromEvidence prf :: diffIsDisjoint
  | (No contra) = diffIsDisjoint
