module CleanRecord.OrdHeader.Label

import CleanRecord.OrdList.Label
import CleanRecord.OrdList.Type
import CleanRecord.OrdHeader.Type

%default total
%access public export

||| Update a value in the list given it's location and an update function
changeType : (xs : OrdHeader k o) -> (loc : OrdLabel l xs) -> (new : Type) ->
             OrdHeader k o
changeType = changeValue
