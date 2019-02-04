module CleanRecord.Selection

import public CleanRecord
import public CleanRecord.SelectionContent

import        Control.Monad.Identity

%default total
%access export


public export
data SelectionM : (m : Type -> Type) ->
                  (source : List (Field label)) ->
                  (header : List (Field label)) -> Type where
  MkSelection : (values : SelectionContentM m source target) ->
                (nubProof : IsNub source) ->
                SelectionM m source target

public export
Selection : (source : List (Field label)) -> (header : List (Field label)) ->
            Type
Selection = SelectionM Identity

sel : (xs : SelectionContentM m source target) ->
      {auto nubProof : IsNub source} ->
      SelectionM m source target
sel xs {nubProof} = MkSelection xs nubProof

namedSel : (xs : NamedSelectionContentM m source target) ->
           {auto nubProof : IsNub source} ->
           SelectionM m source target
namedSel xs {nubProof} = MkSelection (toSelectionContent xs) nubProof

namespace PureSelection

  sel : (xs : PureSelectionContent source target) ->
        {auto nubProof : IsNub source} ->
        Selection source target
  sel xs = sel (toSelectionContent xs)

public export
mapRecordM : Monad m =>
             SelectionM m source target -> Record source ->
             m (Record target)
mapRecordM (MkSelection values nubProof) (MkRecord xs _) = let
  content = mapRecordM values xs
  targetProof = nubSourceTarget values nubProof
  in map (\values' => MkRecord values' targetProof) content

filterMapM : Monad m =>
             SelectionM m source target -> Record header ->
             {auto prf : Sub source header} ->
             m (Record target)
filterMapM statement xs {prf} = mapRecordM statement (project xs)
