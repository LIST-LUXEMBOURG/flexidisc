module CleanRecord.Record.Update

import        CleanRecord.RecordContent
import public CleanRecord.Record.Type

%default total
%access export


||| Replace a row, can change its type
|||
||| Complexity is _O(n)_
|||
||| @ xs  the record
||| @ loc the proof that the row is in it
||| @ new the new value for the row
setByLabel : (xs : Record k header) -> (loc : Label query header) -> (new : ty) ->
      Record k (changeType header loc ty)
setByLabel (Rec xs nub) (L loc) new =
  Rec (set xs loc new) (changeValuePreservesNub nub)

||| Update a row, the update can change the row type.
|||
||| Complexity is _O(n)_
|||
||| @ query the row name
||| @ xs    the record
||| @ loc   the proof that the row is in it
||| @ new   the new value for the row
set : (query : k) -> (new : ty) -> (xs : Record k header) ->
      {auto loc : Label query header} ->
      Record k (changeType header loc ty)
set _ new xs {loc} = setByLabel xs loc new

||| Update a row at a given `Row`, can change its type.
|||
||| Complexity is _O(n)_
|||
||| @ xs     the record
||| @ loc    the proof that the row is in it
||| @ f      the update function
updateByLabel : (xs : Record k header) -> (loc : Row query a header) ->
                (f : a -> b) ->
                Record k (changeType header loc b)
updateByLabel (Rec xs nub) (R loc) f =
  Rec (update xs loc f) (changeValuePreservesNub nub)

||| Update a row at a given `Row`, can change its type.
|||
||| Complexity is _O(n)_
|||
||| @ query  the row name
||| @ xs     the record
||| @ loc    the proof that the row is in it
||| @ f      the update function
update : (query : k) -> (f : a -> b) -> (xs : Record k header) ->
         {auto loc : Row query a header} ->
         Record k (changeType header loc b)
update _ f xs {loc} = updateByLabel xs loc f
