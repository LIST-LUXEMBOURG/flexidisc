module Example.Inject

import Data.Fun
import Data.Vect

import Flexidisc

infixr 8 |->
infix 7 ~~

data (|->) : Type -> Type -> Type where
  F : (a -> b) -> a |-> b

unwrap : (a |-> b) -> a -> b
unwrap (F f) = f

Functor ((|->) a) where
  map g (F f) = F (g . f)

Applicative ((|->) a) where
  pure x = F (const x)
  (<*>) (F f) (F x) = F (\y => f y (x y))

(~~) : (l : k) -> (a -> b) -> TaggedValue l (a |-> b)
(~~) l f = l := F f


Injector : (k : Type) -> Header k -> Type -> Type
Injector k header ty = RecordM ((|->) ty) k header

toRecord : Injector k header src -> src -> Record k header
toRecord inj = unwrap (sequence inj)

field : (l : k) -> {auto loc : Row l ty header} -> (|->) (RecordM m k header) (m ty)
field l {loc} = F $ \r => Read.get l r

namespace typeList

  data TypeList : Vect n k -> Vect n Type -> Header k -> Type where
    Nil  : TypeList [] [] header
    (::) : Row x ty header -> TypeList xs ts header -> TypeList (x::xs) (ty::ts) header

fromRecord : Fun ts a -> (xs : Vect n k) -> Record k header -> {auto prf : TypeList xs ts header} -> a
fromRecord f [] r {prf = []} = f
fromRecord f (_ :: xs) r {prf = (loc::prf)} = fromRecord (f $ r `atRow` loc) xs r

record Person where
  constructor MkPerson
  firstname, lastname: String
  age : Nat


relaxPerson : Person -> Record String ["firstname" ::: String, "lastname" ::: String, "age" ::: Nat]
relaxPerson = toRecord ["firstname" ~~ firstname, "lastname" ~~ lastname, "age" ~~ age]


freezePerson : Record String ["firstname" ::: String, "lastname" ::: String, "age" ::: Nat] -> Person
freezePerson r = fromRecord MkPerson ["firstname", "lastname", "age"] r

