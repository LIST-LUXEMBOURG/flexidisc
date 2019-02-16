module CleanRecord.OrdList.Diff

import public CleanRecord.OrdList.Disjoint
import public CleanRecord.OrdList.Fresh
import public CleanRecord.OrdList.Label
import public CleanRecord.OrdList.Sub
import public CleanRecord.OrdList.Type

%default total
%access public export

diffKeys : DecEq k =>
           (xs : OrdList k v o) -> (ys : OrdList k v o) -> OrdList k v o
diffKeys [] ys = []
diffKeys ((lx, vx) :: xs) ys with (decFresh lx ys)
  | (Yes prf) = (lx, vx) :: diffKeys xs ys
  | (No contra) = diffKeys xs ys

patch : DecEq k =>
        (xs : OrdList k v o) -> (ys : OrdList k v o) -> OrdList k v o
patch xs ys = merge (diffKeys ys xs) xs

diffIsSub : DecEq k => {xs : OrdList k v o} ->
            Sub (diffKeys xs ys) xs
diffIsSub {xs = []} = Empty
diffIsSub {xs = (lx, vx) :: xs} {ys} with (decFresh lx ys)
  | (Yes prf) = Keep diffIsSub
  | (No contra) = Skip diffIsSub

diffIsDisjoint : DecEq k => {xs : OrdList k v o} ->
                 Disjoint (diffKeys xs ys) ys
diffIsDisjoint {xs = []} = []
diffIsDisjoint {xs = (kx, vx) :: xs} {ys} with (decFresh kx ys)
  | (Yes prf) = isFreshFromEvidence prf :: diffIsDisjoint
  | (No contra) = diffIsDisjoint
