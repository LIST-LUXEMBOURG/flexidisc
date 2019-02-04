module CleanRecord.Relation.CompatibleWith

import CleanRecord.IsNo
import CleanRecord.Label
import CleanRecord.Nub
import CleanRecord.Relation.OrdSub
import CleanRecord.Relation.Sub
import CleanRecord.Row

%default total
%access public export

data CompatibleWith : (ref : List (key, value)) -> (xs : List (key, value)) ->
                      Type where
  Empty : CompatibleWith [] xs
  Skip  : DecEq key => {xs : List (key, value)} ->
                       CompatibleWith ref xs -> NotLabel k xs ->
                       CompatibleWith ((k, v)::ref) xs
  Keep  : (loc : Row k ty xs) -> CompatibleWith ref xs ->
          CompatibleWith ((k, ty)::ref) xs

emptyRef : DecEq key => (xs : List (key, value)) -> CompatibleWith [] xs
emptyRef xs = Empty


emptyRec : DecEq key => (ref : List (key, value)) -> CompatibleWith ref []
emptyRec [] = Empty
emptyRec ((k, v) :: xs) = Skip (emptyRec xs) SoFalse
