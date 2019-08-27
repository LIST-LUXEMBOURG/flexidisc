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

implementation Functor (OrdList k o) where

  map f [] = []
  map f ((l, x) :: xs) = (l, f x) :: map f xs

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
merge (x :: hs) [] = (x :: hs)
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