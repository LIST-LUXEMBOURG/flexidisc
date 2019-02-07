module CleanRecord.OrdHeader.Type

%default total
-- Should hide more from it to ensure that we do not mess up with forge header
%access public export

data OrdHeader : (k : Type) -> (Ord k) -> Type where
  Nil  : OrdHeader k o
  (::) : (k, Type) -> OrdHeader k o -> OrdHeader k o

%name OrdHeader hs, xs, ys, zs

insert : (k, Type) -> OrdHeader k o -> OrdHeader k o
insert x []= [x]
insert (k, v) ((k', v') :: xs) with (k < k')
  | False = (k',v') :: (insert (k, v) xs)
  | True  = (k,v)   :: (k',v') :: xs

header : (o : Ord k) => List (k, Type) -> OrdHeader k o
header = foldl (flip insert) Nil

toList : OrdHeader k o -> List (k, Type)
toList [] = []
toList (x :: xs) = x :: toList xs
