module CleanRecord.Selection

import public CleanRecord
import public CleanRecord.SelectionContent

import public Data.Vect

%default total
%access export


public export
data Selection : (source : Vect n (Field label)) ->
                 (header : Vect n (Field label)) -> Type where
  MkSelection : (values : SelectionContent source target) ->
                (nubProof : IsNub source) ->
                Selection source target

sel : (xs : SelectionContent source target) ->
      {auto nubProof : IsNub source} ->
      Selection source target
sel xs {nubProof} = MkSelection xs nubProof

namedSel : (xs : NamedSelectionContent source target) ->
           {auto nubProof : IsNub source} ->
           Selection source target
namedSel xs {nubProof} = MkSelection (toSelectionContent xs) nubProof


select : Selection source target -> Record header ->
         {auto prf : Sub source header} ->
         Record target
select (MkSelection values nubProof) (MkRecord xs _) {prf} =
  MkRecord (select values xs prf) (nubSourceTarget values nubProof)

public export
resultOf : Selection source target -> Type
resultOf x {target} = Record target
