module CleanRecord.Header.Fresh

import CleanRecord.Dec.IsYes
import CleanRecord.Header.Label
import CleanRecord.Header.Type
import CleanRecord.OrdHeader.Fresh as O
import CleanRecord.OrdHeader.Type

%default total
%access public export

data Fresh : (l : label) -> (xs : Header label) -> Type where
  F : (o : Ord k) => {l : k} -> {xs : OrdHeader k o} -> Fresh l xs -> Fresh l (H xs)

private
unpack : (o : Ord k) => {xs : OrdHeader k o} -> Fresh l (H xs) -> Fresh l xs
unpack (F fresh) = fresh

%name Header.Fresh.Fresh fresh, prf, new

IsFresh : (Ord label, DecEq label) => (l : label) -> (xs : Header label) -> Type
IsFresh l (H xs) = IsYes (decFresh l xs)
