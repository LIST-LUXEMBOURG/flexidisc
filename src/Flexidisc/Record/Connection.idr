module Flexidisc.Record.Connection

import Data.Fun
import Data.Vect

import Flexidisc.Record.Read
import Flexidisc.Record.Transformation
import Flexidisc.Record.Type

%default total
%access export

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

||| A type alias for `RecordM` that can be use to inject a given type in a record
public export
Injector : (k : Type) -> Header k -> Type -> Type
Injector k header ty = RecordM ((|->) ty) k header


||| Use an injector to transform a rigid record into a flexible one
toRecord : Injector k header src -> src -> Record k header
toRecord inj = unwrap (sequence inj)

||| A `TypeList` describe how to build a vector of type from a record
data TypeList : Vect n k -> Vect n Type -> Header k -> Type where
  Nil  : TypeList [] [] header
  (::) : Row x ty header -> TypeList xs ts header -> TypeList (x::xs) (ty::ts) header

||| Transform a flexible Record into a rigid one
fromRecord : Fun ts a -> (xs : Vect n k) -> Record k header -> {auto prf : TypeList xs ts header} -> a
fromRecord f [] r {prf = []} = f
fromRecord f (_ :: xs) r {prf = (loc::prf)} = fromRecord (f $ r `atRow` loc) xs r
