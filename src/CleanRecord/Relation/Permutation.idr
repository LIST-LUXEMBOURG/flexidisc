module CleanRecord.Relation.Permutation

import CleanRecord.Elem.Label
import CleanRecord.Elem.Row
import CleanRecord.IsNo
import CleanRecord.Nub

import Data.Vect

%default total
%access public export

||| Proof that a `Vect` is a permutation of another vect
data Permute : (xs : List (key, value)) ->
               (ys : List (key, value)) ->
               Type where
  Empty : Permute [] []
  Keep  : (e : Row k v ys) -> Permute xs (dropRow ys e) ->
          Permute ((k, v)::xs) ys

permuteRefl' : (xs : List (key, value)) -> Permute xs xs
permuteRefl' [] = Empty
permuteRefl' ((k, v)::xs) = Keep Here (permuteRefl' xs)

rowFromPermute :  Permute perm initial -> Label k perm -> Label k initial
rowFromPermute Empty loc = loc
rowFromPermute (Keep e _) Here = labelFromRow e
rowFromPermute (Keep _ xs) (There later) = labelFromDrop (rowFromPermute xs later)

notInPermute : DecEq key =>
               {k: key} -> Permute ys xs -> Not (Label k xs) -> NotLabel k ys
notInPermute perm contra {k} {ys} with (decLabel k ys)
  | (Yes loc) = absurd (contra (rowFromPermute perm loc))
  | (No _) = SoFalse


isNubFromPermute : Permute xs ys -> IsNub ys -> IsNub xs
isNubFromPermute Empty [] = []
isNubFromPermute (Keep e z) (p :: pf) =
  notInPermute z (removeFromNubIsNotThere (p::pf) (labelFromRow e)) ::
  isNubFromPermute z (dropPreservesNub (p::pf))
