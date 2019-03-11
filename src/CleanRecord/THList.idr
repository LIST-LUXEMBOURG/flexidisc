module CleanRecord.THList

%default total
%access export

||| `THList` stands for "TagLess Heterogenous list
||| It's a record demoted to an heterogeneous list,
||| where the label are only kept at the type lebvel
public export
data THList : (k : Type) -> (List (k, Type)) -> Type where
  Nil  : THList k []
  (::) : a -> THList k xs -> THList k ((l, a)::xs)

implementation Eq (THList k []) where
  (==) x y = True
  (/=) x y = False

implementation (Eq t, Eq (THList k ts)) => Eq (THList k ((l,t)::ts)) where
  (==) (x :: xs) (y :: ys) = x == y && xs == ys
  (/=) (x :: xs) (y :: ys) = x /= y || xs /= ys

interface Shows t where
  shows : t -> List String

implementation Shows (THList k []) where
  shows _ = []

implementation (Show k, Show t, Shows (THList k ts)) => Shows (THList k ((l,t) :: ts)) where
  shows (x::xs) {l} = unwords [show l, ":=", show x] :: shows xs

implementation Shows (THList k xs) => Show (THList k xs) where
  show xs = unwords ["[", concat (intersperse ", " (shows xs)), "]"]
