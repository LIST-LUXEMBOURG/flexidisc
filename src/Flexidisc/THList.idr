module Flexidisc.THList

%default total
%access export

||| `THList` stands for "TagLess Heterogenous list
||| It's a record demoted to an heterogeneous list,
||| where the label are only kept at the type lebvel
public export
data THList : (m : Type -> Type) -> (k : Type) -> (List (k, Type)) -> Type where
  Nil  : THList m k []
  (::) : m a -> THList m k xs -> THList m k ((l, a)::xs)

implementation Eq (THList m k []) where
  (==) x y = True
  (/=) x y = False

implementation (Eq (m t), Eq (THList m k ts)) => Eq (THList m k ((l,t)::ts)) where
  (==) (x :: xs) (y :: ys) = x == y && xs == ys
  (/=) (x :: xs) (y :: ys) = x /= y || xs /= ys

interface Shows t where
  shows : t -> List String

implementation Shows (THList m k []) where
  shows _ = []

implementation (Show k, Show (m t), Shows (THList m k ts)) =>
               Shows (THList m k ((l,t) :: ts)) where
  shows (x::xs) {l} = unwords [show l, ":=", show x] :: shows xs

implementation Shows (THList m k xs) => Show (THList m k xs) where
  show xs = unwords ["[", concat (intersperse ", " (shows xs)), "]"]
