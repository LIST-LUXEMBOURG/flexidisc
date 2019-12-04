module Example.Inject

import Data.Fun
import Data.Vect

import Flexidisc

record Person where
  constructor MkPerson
  firstname, lastname: String
  age : Nat


relaxPerson : Person -> Record String ["firstname" ::: String, "lastname" ::: String, "age" ::: Nat]
relaxPerson = toRecord ["firstname" ~~ firstname, "lastname" ~~ lastname, "age" ~~ age]


freezePerson : Record String ["firstname" ::: String, "lastname" ::: String, "age" ::: Nat] -> Person
freezePerson r = fromRecord MkPerson ["firstname", "lastname", "age"] r
