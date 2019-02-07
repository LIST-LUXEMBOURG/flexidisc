module CleanRecord.Header.Permute

import CleanRecord.Header.Fresh
import CleanRecord.Header.Nub
import CleanRecord.Header.Type
import CleanRecord.OrdHeader.Fresh
import CleanRecord.OrdHeader.Nub
import CleanRecord.OrdHeader.Permute as P
import CleanRecord.OrdHeader.Type

%default total
%access public export

||| Proof that a `Vect` is a permutation of another vect
data Permute : (xs : Header k) -> (ys : Header k) -> Type where
  P : (o : Ord k) =>
      {xs : OrdHeader k o} -> {ys : OrdHeader k o} ->
      Permute xs ys -> Permute (H xs) (H ys)


freshInsert : (DecEq k, Ord k) =>
              {k' : k} -> {header : Header k} ->
              IsFresh k' header -> Nub header ->
              Nub ((k', ty) :: header)
freshInsert fresh (N isnub) = N (P.freshInsert fresh isnub)
