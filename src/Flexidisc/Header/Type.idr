||| `Header` is a wrapper for `OrdList` that hides the order relationship
||| and allows order independent list syntax for headers fields declaration.
|||
||| For example
||| `the (Header Char) ['a' ::: String, 'b' ::: Bool] = the (Header Char) ['b' ::: Bool, 'a' ::: String]`
||| holds.
|||
||| While `Header` doesn't define the usual `List` constructors,
||| the `List` syntax is available (and should be use)
||| as both `Nil` and `::` are defined for `Header`
module Flexidisc.Header.Type

import Flexidisc.OrdList

%default total
%access public export

||| Wrapper for `OrdList` that hide the order relationship
data Header' : (k : Type) -> (t : Type) -> Type where
  H : (o : Ord k) => OrdList k o t -> Header' k t

||| Wrapper for `OrdList` that hide the order relationship
Header : (k : Type) -> Type
Header k = Header' k Type

||| Extract the wrapped `OrdList` along with it's order relation
unwrap : Header' k a -> (o ** OrdList k o a)
unwrap (H hs) = (_ ** hs)

||| A helper for the empty header creation
Nil : Ord k => Header' k a
Nil = H []

||| Append actually called insert on the underlying `OrdList`, to ensure that
||| the header labels are sorted
(::) : (k, a) -> Header' k a -> Header' k a
(::) x (H h) = H (insert x h)

merge : Header' k a -> Header' k a -> Header' k a
merge (H xs) (H ys) = H (merge xs ys)

toList : Header' k a -> List (k, a)
toList (H xs) = toList xs

optional : Header k -> Header k
optional (H xs) = H (map Maybe xs)
