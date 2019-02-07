module CleanRecord.THList

%default total
%access export

||| `THList` stands for "TagLess Heterogenous list
||| It's a record demoted to an heterogeneous list,
||| where the label are only kept at the type lebvel
public export
data THList : (List (k, Type)) -> Type where
  Nil  : THList []
  (::) : a -> THList xs -> THList ((l, a)::xs)

implementation Eq (THList []) where
  (==) x y = True
  (/=) x y = False

implementation (Eq t, Eq (THList ts)) => Eq (THList ((k,t)::ts)) where
  (==) (x :: xs) (y :: ys) = x == y && xs == ys
  (/=) (x :: xs) (y :: ys) = x /= y || xs /= ys
