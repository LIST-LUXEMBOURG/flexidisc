module Flexidisc.OrdList.Permute

import Flexidisc.OrdList.Fresh
import Flexidisc.OrdList.Label
import Flexidisc.OrdList.Nub
import Flexidisc.OrdList.Row
import Flexidisc.OrdList.Type

%default total
%access private

||| Proof that an `OrdList` is a permutation of another `OrdList`
public export
data Permute : (xs : OrdList k o1 v) ->
               (ys : OrdList k o2 v) ->
               Type where
  ||| The empty list is a permutation of an empty list
  Empty : Permute [] []
  Keep  : (e : OrdRow k ty ys) -> Permute xs (dropOrdRow ys e) ->
          Permute ((k, ty)::xs) ys

permuteRefl : (xs : OrdList k o v) -> Permute xs xs
permuteRefl [] = Empty
permuteRefl ((k, v)::xs) = Keep Here (permuteRefl xs)

insertConsPermute : (x : (k, v)) -> (xs : OrdList k o v) ->
                    Permute  (insert x xs) (x :: xs)
insertConsPermute (k, ty) [] = Keep Here Empty
insertConsPermute (k, ty) ((kx, tx) :: xs) with (k < kx)
  | True  = Keep Here (Keep Here (permuteRefl xs))
  | False = Keep (There Here) (insertConsPermute (k, ty) xs)

consInsertPermute : (x : (k, v)) -> (xs : OrdList k o v) ->
                    Permute  (x :: xs) (insert x xs)
consInsertPermute (l, ty) xs =
  Keep (findInsertOrdRow l xs)
       (rewrite dropInsertInv l ty xs in (permuteRefl xs))

permutePreservesFresh :  Permute ys xs -> Fresh k xs -> Fresh k ys
permutePreservesFresh Empty [] = []
permutePreservesFresh (Keep e perm) fresh =
  (\p => freshCantBeLabel fresh (rewrite p in labelFromOrdRow e)) ::
  permutePreservesFresh perm (dropPreservesFresh fresh)

isNubFromPermute : Permute xs ys -> Nub ys -> Nub xs
isNubFromPermute Empty [] = []
isNubFromPermute (Keep e perm) pf =
  permutePreservesFresh perm (removeFromNubIsFresh pf (labelFromOrdRow e))
    :: isNubFromPermute perm (dropPreservesNub pf (labelFromOrdRow e))

export
freshInsert : Fresh k' header -> Nub header ->
              Nub (insert (k', ty) header)
freshInsert fresh isnub {k'} {ty} {header} =
  isNubFromPermute (insertConsPermute (k', ty) header) (fresh :: isnub)
