module CleanRecord.Header.Type

import CleanRecord.OrdHeader.Type

%default total
%access public export

data Header : (k : Type) -> Type where
  H : (o : Ord k) => OrdHeader k o -> Header k

unwrap : Header k -> (o ** OrdHeader k o)
unwrap (H hs) = (_ ** hs)

Nil : Ord k => Header k
Nil = H []

(::) : (k, Type) -> Header k -> Header k
(::) x (H h) = H (insert x h)

toList : Header k -> List (k, Type)
toList (H xs) = toList xs
