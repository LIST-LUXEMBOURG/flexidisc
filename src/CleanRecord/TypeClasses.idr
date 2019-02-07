module CleanRecord.TypecClasses

import CleanRecord.Elem.Label

import CleanRecord.IsNo
import CleanRecord.Nub

%default total
%access  export

infix 8 :=

namespace Field

  Field : Type -> Type
  Field label = (label, Type)

  (:=) : label -> Type -> Field label
  (:=) = MkPair

public export
data TaggedValue : (l : label) -> Type -> Type where
  (:=) : (l : label) -> a -> TaggedValue l a


data Key : (label : Type) -> (l : label) -> Type where
  MkKey : (l : label) -> Key label l

implicit
toKey : (l : label) -> Key label l
toKey = MkKey

data Record : (label : Type) -> (header : List (Field label)) -> Type where
  Nil  : Record label []
  (::) : a -> Record label header -> Record label ((l,a) :: header) 

interface NotEq (label : Type) (x : label) (y : label) (prf : Dec (x = y)) where

implementation DecEq xs => NotEq label x y (No contra) where

data PromoteNEQ : (Dec (x = y)) -> Type where
  P : PromoteNEQ contra

insertNub : (Key String x) -> (a : tx) -> Record String [(y,ty)] -> {default SoFalse prf : NotLabel x
            [(y,ty)]} -> Record String [(x,tx),(y,ty)]
insertNub x a y = a::y

test : Record String [("Foo", Bool), ("Bar", String)]
test = insertNub "Foo" True ["Fooooooo"]

{-
interface HasType (label : Type) (l : label) (ty : Type) (header : List (Field label))
  | label, header where
  -- (k : Key label l) (ty : Type) (header : List (Field label)) where
  get : (Key label l) -> (Record label header) -> ty

implementation HasType label k v ((k,v)::xs) where
  get k (x::xs) = x

implementation HasType label k v xs => HasType label k v (_::xs) where
  get k (_::xs) = get k xs
  -}
