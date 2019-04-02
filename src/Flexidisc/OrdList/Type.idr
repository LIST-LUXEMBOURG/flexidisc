||| OrdList are labelled list (key/value store) that embed a order relation on keys
||| to sort its elements.
module Flexidisc.OrdList.Type

%default total
%access public export

||| The OrdList consturctors are exported publicly as they need to be used at
||| the type level.
||| It's better not to use the constructor for something else that just patter
||| matching, as they dont guarantee that the keys are ordered.
data OrdList : (k : Type) -> (v : Type) -> (o : Ord k) -> Type where
  Nil  : OrdList k v o
  (::) : (k, v) -> OrdList k v o -> OrdList k v o

%name OrdList xs, ys, zs

||| Insert an element in the list before the first element that is greater than
||| the given one.
insert : (k, v) -> OrdList k v o -> OrdList k v o
insert x []= [x]
insert (k, v) ((k', v') :: xs) with (k < k')
  | False = (k',v') :: (insert (k, v) xs)
  | True  = (k,v)   :: (k',v') :: xs

||| Merge to `OrdList`, preserving the order if the initial list are ordered.
merge :  OrdList k v o -> OrdList k v o -> OrdList k v o
merge [] xs = xs
merge (x :: hs) [] = (x :: hs)
merge ((k, v) :: hs) ((k', v') :: xs) with (k < k')
  | False = (k', v') :: merge ((k, v) :: hs) xs
  | True  = (k , v)  :: merge hs ((k', v') :: xs)

||| Apply a function to all values
mapValues : (v -> v') -> OrdList k v o -> OrdList k v' o
mapValues f [] = []
mapValues f ((l, x) :: xs) = (l, f x) :: mapValues f xs

||| Sort a list.
toOrdList : (o : Ord k) => List (k, v) -> OrdList k v o
toOrdList = foldl (flip insert) Nil

||| Morphism to a list.
toList : OrdList k v o -> List (k, v)
toList [] = []
toList (x :: xs) = x :: toList xs
