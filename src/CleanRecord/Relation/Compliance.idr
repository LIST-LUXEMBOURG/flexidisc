module CleanRecord.Relation.Compliance

import CleanRecord.IsNo
import CleanRecord.Label
import CleanRecord.Nub
import CleanRecord.Relation.OrdSub
import CleanRecord.Relation.Sub
import CleanRecord.Row

%default total
%access public export

data Compliance : (xs : List (key, value)) ->
                  (ref : List (key, value)) ->
                  Type where
  Empty : Compliance xs []
  Skip  : DecEq key => {xs : List (key, value)} ->
                       Compliance xs ref -> NotLabel k xs ->
                       Compliance xs ((k, v)::ref)
  Keep  : (loc : Row k ty xs) -> Compliance xs ref ->
          Compliance xs ((k, ty)::ref)

emptyRef : DecEq key => (xs : List (key, value)) -> Compliance xs []
emptyRef xs = Empty


emptyRec : DecEq key => (ref : List (key, value)) -> Compliance [] ref
emptyRec [] = Empty
emptyRec ((k, v) :: xs) = Skip (emptyRec xs) SoFalse
