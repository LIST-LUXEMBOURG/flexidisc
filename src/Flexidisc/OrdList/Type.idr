||| OrdList are labelled list (key/value store) that embed a order relation on keys
||| to sort its elements.
module Flexidisc.OrdList.Type

%default total
%access public export

||| The OrdList consturctors are exported publicly as they need to be used at
||| the type level.
||| It's better not to use the constructor for something else that just pattern
||| matching, as they dont guarantee that the keys are ordered.
||| @k Type of the keys
||| @v Type of the values
||| @o The order relation used to compared keys
data OrdList : (k : Type) ->  (o : Ord k) -> (v : Type) -> Type where
  Nil  : OrdList k o v
  (::) : (k, v) -> OrdList k o v -> OrdList k o v

%name OrdList xs, ys, zs

keys : OrdList k o v -> List k
keys [] = []
keys (kv :: xs) = fst kv :: keys xs

implementation Functor (OrdList k o) where

  map f [] = []
  map f (kv :: xs) = map f kv :: map f xs

||| Insert an element in the list before the first element that is greater than
||| the given one., according to the order `o`
insert : (x : (k, v)) -> (xs : OrdList k o v) -> OrdList k o v
insert x []= [x]
insert (k, v) ((k', v') :: xs) with (k < k')
  | False = (k',v') :: (insert (k, v) xs)
  | True  = (k,v)   :: (k',v') :: xs

||| Merge two `OrdList`, preserving the order if the initial list are ordered.
merge :  OrdList k o v -> OrdList k o v -> OrdList k o v
merge [] xs = xs
merge xs [] = xs
merge ((k, v) :: hs) ((k', v') :: xs) with (k < k')
  | False = (k', v') :: merge ((k, v) :: hs) xs
  | True  = (k , v)  :: merge hs ((k', v') :: xs)

||| Sort a list.
toOrdList : (o : Ord k) => List (k, v) -> OrdList k o v
toOrdList = foldl (flip insert) Nil

||| Morphism to a list.
toList : OrdList k o v -> List (k, v)
toList [] = []
toList (x :: xs) = x :: toList xs

namespace properties

  mapPreservesKeys : (xs : OrdList k o v) -> (f : v-> v') ->
                     keys xs = keys (map f xs)
  mapPreservesKeys [] f = Refl
  mapPreservesKeys ((a, b) :: xs) f = cong $ mapPreservesKeys xs f
