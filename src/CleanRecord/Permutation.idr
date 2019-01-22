module CleanRecord.Permutation

import CleanRecord.Row
import CleanRecord.IsNo
import CleanRecord.Nub
import CleanRecord.OrdSub

import Data.Vect

%default total
%access public export


data Permute : (permute : Vect n (key, value)) ->
               (initial : Vect n (key, value)) ->
               Type where
  Empty : Permute [] []
  Keep  : (e : Row k v initial) -> Permute permute (dropRow initial e) ->
          Permute ((k, v)::permute) initial

permuteRefl' : (xs : Vect n (key, value)) -> Permute xs xs
permuteRefl' [] = Empty
permuteRefl' ((k, v)::xs) = Keep Here (permuteRefl' xs)

rowFromPermute :  Permute perm initial -> Row k v perm -> Row k v initial
rowFromPermute Empty loc = loc
rowFromPermute (Keep e _) Here = e
rowFromPermute (Keep _ xs) (There later) = rowFromDrop (rowFromPermute xs later)

notInPermute : DecEq key =>
               {k: key} -> Permute ys xs -> Not (v ** Row k v xs) -> NotKey k ys
notInPermute perm contra {k} {ys} with (decKey k ys)
  | (Yes (t ** loc)) = absurd (contra (t ** rowFromPermute perm loc))
  | (No _) = SoFalse


isNubFromPermute : Permute xs ys -> IsNub ys -> IsNub xs
isNubFromPermute Empty [] = []
isNubFromPermute (Keep e z) (p :: pf) =
  notInPermute z (removeFromNubIsNotThere (p::pf) e) ::
  isNubFromPermute z (isNubFromOrdSub (ordSubFromDrop _ (labelFromRow e)) (p::pf))
