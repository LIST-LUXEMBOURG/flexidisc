module Flexidisc.Record.Update

import        Flexidisc.RecordContent
import public Flexidisc.Record.Type

%default total
%access export


||| Replace a row, can change its type
|||
||| Complexity is _O(n)_
|||
||| @ xs  the record
||| @ loc the proof that the row is in it
||| @ new the new value for the row
setByLabel : (xs : RecordM m k header) -> (loc : Label query header) ->
             (new : m ty) ->
             RecordM m k (changeType header loc ty)
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
set : (query : k) -> (new : m ty) -> (xs : RecordM m k header) ->
      {auto loc : Label query header} ->
      RecordM m k (changeType header loc ty)
set _ new xs {loc} = setByLabel xs loc new

||| Update a row, the update can change the row type.
|||
||| Complexity is _O(n)_
|||
||| @ query the row name
||| @ xs    the record
||| @ loc   the proof that the row is in it
||| @ new   the new value for the row
setA : Applicative m =>
       (query : k) -> (new : ty) -> (xs : RecordM m k header) ->
       {auto loc : Label query header} ->
       RecordM m k (changeType header loc ty)
setA loc = set loc . pure

||| Update a row at a given `Row`, can change its type.
|||
||| Complexity is _O(n)_
|||
||| @ xs     the record
||| @ loc    the proof that the row is in it
||| @ f      the update function
updateByLabel : (xs : RecordM m k header) -> (loc : Row query a header) ->
                (f : m a -> m b) ->
                RecordM m k (changeType header loc b)
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
update : (query : k) -> (f : m a -> m b) -> (xs : RecordM m k header) ->
         {auto loc : Row query a header} ->
         RecordM m k (changeType header loc b)
update _ f xs {loc} = updateByLabel xs loc f

||| Map at a given `Row`, can change its type.
|||
||| Complexity is _O(n)_
|||
||| @ query  the row name
||| @ xs     the record
||| @ loc    the proof that the row is in it
||| @ f      the update function
mapRow : Functor m =>
         (query : k) -> (f : a -> b) -> (xs : RecordM m k header) ->
         {auto loc : Row query a header} ->
         RecordM m k (changeType header loc b)
mapRow _ f xs {loc} = updateByLabel xs loc (map f)
