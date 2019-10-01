module Flexidisc.Record.Endo

import        Flexidisc.RecordContent
import public Flexidisc.Record.Type

%default total
%access export


||| Update a row at a given `Row`, can change its type.
|||
||| Complexity is _O(n)_
|||
||| @ xs     the record
||| @ loc    the proof that the row is in it
||| @ f      the update function
updateByLabel : (xs : Record k header) -> (loc : Row query a header) ->
                (f : a -> a) ->
                Record k header
updateByLabel (Rec xs nub) (R loc) f =
  rewrite sym (changeWithSameTypeIsUnchanged loc) in
          Rec (update xs loc f) (changeValuePreservesNub nub)

||| Update a row at a given `Row`, can change its type.
|||
||| Complexity is _O(n)_
|||
||| @ query  the row name
||| @ xs     the record
||| @ loc    the proof that the row is in it
||| @ f      the update function
update : (query : k) -> (f : a -> a) -> (xs : Record k header) ->
         {auto loc : Row query a header} ->
         Record k header
update _ f xs {loc} = updateByLabel xs loc f

||| Replace a row, can change its type
|||
||| Complexity is _O(n)_
|||
||| @ xs  the record
||| @ loc the proof that the row is in it
||| @ new the new value for the row
setByLabel : (xs : Record k header) -> (loc : Row query ty header) ->
             (new : ty) ->
             Record k header
setByLabel xs loc new = updateByLabel xs loc (const new)

||| Update a row, the update can change the row type.
|||
||| Complexity is _O(n)_
|||
||| @ query the row name
||| @ xs    the record
||| @ loc   the proof that the row is in it
||| @ new   the new value for the row
set : (query : k) -> (new : ty) -> (xs : Record k header) ->
      {auto loc : Row query ty header} ->
      Record k header
set _ new xs {loc} = updateByLabel xs loc (const new)
