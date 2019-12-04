module Flexidisc.OrdList.Diff

import public Flexidisc.OrdList.Disjoint
import public Flexidisc.OrdList.Fresh
import public Flexidisc.OrdList.Label
import public Flexidisc.OrdList.Sub
import public Flexidisc.OrdList.Type

%default total
%access public export

||| compute the difference between the first and the second list.
diffKeys : DecEq k =>
           (xs : OrdList k v o) -> (ys : OrdList k v o) -> OrdList k v o
diffKeys [] ys = []
diffKeys ((lx, vx) :: xs) ys with (decFresh lx ys)
  | Yes prf   = (lx, vx) :: diffKeys xs ys
  | No contra = diffKeys xs ys

||| Apply a patch `xs` to an `OrdList` `ys`.
||| The label of `ys` that are in `xs` are updated,
||| and the fresh element of `xs` are added
patch : DecEq k =>
        (xs : OrdList k v o) -> (ys : OrdList k v o) -> OrdList k v o
patch xs ys = merge (diffKeys ys xs) xs

diffIsSub : DecEq k => {xs : OrdList k v o} ->
            Sub (diffKeys xs ys) xs
diffIsSub {xs = []} = Empty
diffIsSub {xs = (lx, vx) :: xs} {ys} with (decFresh lx ys)
  | Yes prf   = Keep diffIsSub
  | No contra = Skip diffIsSub

diffIsDisjoint : DecEq k => {xs : OrdList k v o} ->
                 Disjoint (diffKeys xs ys) ys
diffIsDisjoint {xs = []} = []
diffIsDisjoint {xs = (kx, vx) :: xs} {ys} with (decFresh kx ys)
  | Yes prf  = isFreshFromEvidence prf :: diffIsDisjoint
  | No contra = diffIsDisjoint
