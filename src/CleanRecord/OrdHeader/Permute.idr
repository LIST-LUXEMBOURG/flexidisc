module CleanRecord.OrdHeader.Permute

import CleanRecord.OrdHeader.Fresh
import CleanRecord.OrdHeader.Label
import CleanRecord.OrdHeader.Nub
import CleanRecord.OrdHeader.Row
import CleanRecord.OrdHeader.Type

%default total
%access private

||| Proof that a `Vect` is a permutation of another vect
public export
data Permute : (xs : OrdHeader k o) ->
               (ys : OrdHeader k o) ->
               Type where
  Empty : Permute [] []
  Keep  : (e : OrdRow k ty ys) -> Permute xs (dropOrdRow ys e) ->
          Permute ((k, ty)::xs) ys

permuteRefl : (xs : OrdHeader k o) -> Permute xs xs
permuteRefl [] = Empty
permuteRefl ((k, v)::xs) = Keep Here (permuteRefl xs)

insertConsPermute : (x : (k, Type)) -> (xs : OrdHeader k o) ->
                    Permute  (insert x xs) (x :: xs)
insertConsPermute (k, ty) [] = Keep Here Empty
insertConsPermute (k, ty) ((kx, tx) :: xs) with (k < kx)
  | True  = Keep Here (Keep Here (permuteRefl xs))
  | False = Keep (There Here) (insertConsPermute (k, ty) xs)

consInsertPermute : (x : (k, Type)) -> (xs : OrdHeader k o) ->
                    Permute  (x :: xs) (insert x xs)
consInsertPermute (l, ty) xs =
  Keep (findInsertOrdRow l xs)
       (rewrite dropInsertInv l ty xs in (permuteRefl xs))

permutePreservesFresh :  Permute ys xs -> Fresh k xs -> Fresh k ys
permutePreservesFresh Empty fresh = fresh
permutePreservesFresh (Keep e perm) fresh =
  (\p => freshCantBeLabel fresh (rewrite p in labelFromOrdRow e)) ::
  permutePreservesFresh perm (dropPreservesFresh fresh)

isNubFromPermute : Permute xs ys -> Nub ys -> Nub xs
isNubFromPermute Empty [] = []
isNubFromPermute (Keep e perm) pf@(p::_) =
  isFreshFromEvidence
    (permutePreservesFresh perm (removeFromNubIsFresh pf (labelFromOrdRow e)))
  :: isNubFromPermute perm (dropPreservesNub pf (labelFromOrdRow e))

export
freshInsert : (DecEq k, Ord k) =>
              {k' : k} ->
              IsFresh k' header -> Nub header ->
              Nub (insert (k', ty) header)
freshInsert fresh isnub {k'} {ty} {header} =
  isNubFromPermute (insertConsPermute (k', ty) header) (fresh :: isnub)
