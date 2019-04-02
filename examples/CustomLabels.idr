||| This example follows the same framework as the tutorial, but with custom labels
||| We use a custom datatype for labels instead of `String`.
module Flexidisc.CustomLabels

import Flexidisc
import Flexidisc.InjectiveDecEq

export
data Feature = Firstname | Lastname | Age | ID

implementation
InjectiveDecEq Feature Nat where

  inj Firstname = 0
  inj Lastname  = 1
  inj Age       = 2
  inj ID        = 3

  ret Z             = Firstname
  ret (S Z)         = Lastname
  ret (S (S Z))     = Age
  ret (S (S (S k))) = ID

  inv Firstname = Refl
  inv Lastname  = Refl
  inv Age       = Refl
  inv ID        = Refl

implementation Eq Feature where
 (==) x y = (==) (inj x) (inj y)

implementation Ord Feature where
  compare x y = compare (inj x) (inj y)

person0 : Record Feature [Firstname ::: String]
person0 = [Firstname := "John"]

||| From here, we can access row by name.
|||
||| Fields are verified at compile time: if we try to access a field that is
||| not defined for our record, we obtain a compilation error, not a runtime
||| error.
|||
||| One of the key contribution in Flexidisc is that you can't declare the
||| smae field twice (no, it's not that easy)
||| If we add another field 'Firstname', even with a different type,
||| we'll obtain a compilation error.
person0Name : String
person0Name = get Firstname person0

||| or with the infix notation:
person0Name' : String
person0Name' = person0 !! Firstname

||| you can even lookup for fields that my or may not be there
person0age : Maybe Nat
person0age = lookup Age person0

||| We can of course extend records:
||| we can use either the definition below or `person1 = ["Biri", "Nicolas"]
person1 : Record Feature [Age ::: Nat, Lastname ::: String, Firstname ::: String]
person1 = (Lastname := "Doe") :: (Age := the Nat 42) :: person0
