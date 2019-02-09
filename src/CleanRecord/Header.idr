module CleanRecord.Header

import public CleanRecord.Header.CompWithKeys
import public CleanRecord.Header.Disjoint
import public CleanRecord.Header.Fresh
import public CleanRecord.Header.HereOrNot
import public CleanRecord.Header.Label
import public CleanRecord.Header.Nub
import public CleanRecord.Header.Row
import public CleanRecord.Header.Sub
import public CleanRecord.Header.SubWithKeys
import public CleanRecord.Header.Type

import CleanRecord.OrdHeader

%default total
%access public export


comp : DecEq k => (xs : Header k) -> (ys : Header k) -> Header k
comp (H xs) (H ys) = H (comp xs ys)

{-
disjointComp : DecEq k => (xs : Header k) -> (ys : Header k) ->
                          Disjoint (comp xs ys) ys
disjointComp (H xs) (H ys) = ?disjointComp_rhs_2
-}
