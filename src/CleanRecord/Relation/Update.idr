module CleanRecord.Relation.Update

import CleanRecord.Label
import CleanRecord.Nub

import Data.Vect

%default total
%access public export

data Patch : Vect m (key, value) -> Vect n (key, value) -> Vect n (key, value) -> Type where
  Nil : Patch [] xs xs
  (::) : (loc : Label k pre) ->
         (next : Patch update (updateLabel pre loc new) post) ->
         Patch ((k, new)::update) pre post

patchPreservesNub : (prf : IsNub pre) -> (patch : Patch upd pre post) -> IsNub post
patchPreservesNub prf [] = prf
patchPreservesNub prf (loc :: next) = patchPreservesNub (updatePreservesNub prf) next
