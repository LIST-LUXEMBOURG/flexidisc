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


comp : DecEq k => (xs : OrdHeader k o1) -> (ys : OrdHeader k o2) -> OrdHeader k o1
comp [] ys = []
comp ((k, v) :: hs) ys with (decFresh k ys)
  | Yes _ = (k, v) :: comp hs ys
  | No  _ = comp hs ys

disjointComp : DecEq k => (xs : OrdHeader k o1) -> (ys : OrdHeader k o2) ->
                          Disjoint (comp xs ys) ys
disjointComp [] ys = []
disjointComp ((k, v) :: hs) ys with (decFresh k ys)
  | (Yes prf) = isFreshFromEvidence prf :: disjointComp hs ys
  | (No contra) = disjointComp hs ys
