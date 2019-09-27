module Example.Inject

import Flexidisc

infixr 8 |->
infix 7 ~~

data (|->) : Type -> Type -> Type where
  F : (a -> b) -> a |-> b

unwrap : (a |-> b) -> a -> b
unwrap (F f) = f

Functor ((|->) b) where
  map g (F f) = F (g . f)

Applicative ((|->) b) where
  pure x = F (const x)
  (<*>) (F f) (F x) = F (\y => f y (x y))

(~~) : (l : k) -> (a -> b) -> TaggedValue l (a |-> b)
(~~) l f = l := F f


record Person where
  constructor MkPerson
  firstname, lastname: String
  age : Nat

inject : Person -> Record String ["firstname" ::: String, "lastname" ::: String, "age" ::: Nat]
inject = unwrap $ sequence ["firstname" ~~ firstname, "lastname" ~~ lastname, "age" ~~ age]
