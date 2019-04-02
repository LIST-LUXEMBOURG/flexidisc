module Flexidisc.OrdHeader

import public Flexidisc.OrdList

%default total
%access public export

||| An alias for `OrdList` that ensures that the values are `Type`
OrdHeader : (k : Type) -> (o : Ord k) -> Type
OrdHeader k o = OrdList k Type o

||| Update a value in the list given it's location and an update function
changeType : (xs : OrdHeader k o) -> (loc : OrdLabel l xs) -> (new : Type) ->
             OrdHeader k o
changeType = changeValue

||| Make types optional (encapsulate them in `Maybe`)
optional : OrdHeader k o -> OrdHeader k o
optional = mapValues Maybe
