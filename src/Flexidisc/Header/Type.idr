module Flexidisc.Header.Type

import Flexidisc.OrdHeader

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

merge : Header k -> Header k -> Header k
merge (H xs) (H ys) = H (merge xs ys)

toList : Header k -> List (k, Type)
toList (H xs) = toList xs

optional : Header k -> Header k
optional (H xs) = H (optional xs)
