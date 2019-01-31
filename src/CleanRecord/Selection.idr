module CleanRecord.Selection

import public CleanRecord
import public CleanRecord.SelectionContent

import public Data.List

%default total
%access export


public export
data SelectionM : (m : Type -> Type) ->
                  (source : List (Field label)) ->
                  (header : List (Field label)) -> Type where
  MkSelection : (values : SelectionContentM m source target) ->
                (nubProof : IsNub source) ->
                SelectionM m source target

sel : (xs : SelectionContentM m source target) ->
      {auto nubProof : IsNub source} ->
      SelectionM m source target
sel xs {nubProof} = MkSelection xs nubProof

namedSel : (xs : NamedSelectionContentM m source target) ->
           {auto nubProof : IsNub source} ->
           SelectionM m source target
namedSel xs {nubProof} = MkSelection (toSelectionContent xs) nubProof


filterMapM : Monad m =>
             SelectionM m source target -> Record header ->
             {auto prf : Sub source header} ->
             m (Record target)
filterMapM (MkSelection values nubProof) (MkRecord xs _) {prf} = let
  content = filterMapM values xs prf
  targetProof = nubSourceTarget values nubProof
  in map (\values' => MkRecord values' targetProof) content
