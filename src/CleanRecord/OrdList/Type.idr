module CleanRecord.OrdList.Type

%default total
%access public export

data OrdList : (k : Type) -> (v : Type) -> (o : Ord k) -> Type where
  Nil  : OrdList k v o
  (::) : (k, v) -> OrdList k v o -> OrdList k v o

%name OrdList xs, ys, zs

insert : (k, v) -> OrdList k v o -> OrdList k v o
insert x []= [x]
insert (k, v) ((k', v') :: xs) with (k < k')
  | False = (k',v') :: (insert (k, v) xs)
  | True  = (k,v)   :: (k',v') :: xs

merge :  OrdList k v o -> OrdList k v o -> OrdList k v o
merge [] xs = xs
merge (x :: hs) [] = (x :: hs)
merge ((k, v) :: hs) ((k', v') :: xs) with (k < k')
  | False = (k', v') :: merge ((k, v) :: hs) xs
  | True  = (k , v)  :: merge hs ((k', v') :: xs)

toOrdList : (o : Ord k) => List (k, v) -> OrdList k v o
toOrdList = foldl (flip insert) Nil

toList : OrdList k v o -> List (k, v)
toList [] = []
toList (x :: xs) = x :: toList xs
