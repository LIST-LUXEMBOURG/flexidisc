module Flexidisc.Transformation.TransHeader

import Flexidisc.Dec.IsYes
import Flexidisc.Header.Type
import Flexidisc.OrdList
import Flexidisc.OrdHeader
import Flexidisc.Transformation.Type

%default total
%access public export

data TransHeader : (k : Type) -> Type where
  T : (o : Ord k) => OrdList k o MapValue -> TransHeader k

Nil : Ord k => TransHeader k
Nil = T []

(::) : (k, MapValue) -> TransHeader k -> TransHeader k
(::) x (T h) = T (insert x h)

IsFresh : (DecEq label) => (l : label) -> (xs : TransHeader label) -> Type
IsFresh l (T xs) = IsYes (decFresh l xs)

toLabels : TransHeader k -> List k
toLabels (T xs) = toLabels xs

toSource : TransHeader k -> Header k
toSource (T xs) = H (toSource xs)

toTarget : TransHeader k -> Header k
toTarget (T xs) = H (toTarget xs)
