module Flexidisc.Function

import Flexidisc.TaggedValue

%default total
%access public export

infixr 8 |->
infix 7 ~~

||| A wrapper for functions to allow definition of typeclasses
record (|->) (a : Type) (b : Type) where
  constructor F
  unwrap : (a -> b)


Functor ((|->) a) where
  map g (F f) = F (g . f)

Applicative ((|->) a) where
  pure x = F (const x)
  (<*>) (F f) (F x) = F (\y => f y (x y))

(~~) : (l : k) -> (a -> b) -> TaggedValue l (a |-> b)
(~~) l f = l := F f
