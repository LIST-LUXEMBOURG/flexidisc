module CleanRecord.Selection

import public CleanRecord.Record
import public CleanRecord.Selection.SelectionContent

import        Control.Monad.Identity

%default total
%access export


public export
data SelectionM : (m : Type -> Type) -> (mapper : List (MapValue label)) -> Type where
  MkSelection : (values : MapValuesM m mapper) ->
                (nubProof : IsNub (toSource mapper)) ->
                SelectionM m mapper

public export
Selection : (mapper : List (MapValue label)) -> Type
Selection = SelectionM Identity

sel : (xs : MapValuesM m mapper) -> {auto nubProof : IsNub (toSource mapper)} ->
      SelectionM m mapper
sel xs {nubProof} = MkSelection xs nubProof

namedSel : (xs : NamedMapValuesM m mapper) ->
           {auto nubProof : IsNub (toSource mapper)} ->
           SelectionM m mapper
namedSel xs {nubProof} = MkSelection (toMapValuesM xs) nubProof

namespace PureSelection

  sel : (xs : PureMapValues mapper) -> {auto nubProof : IsNub (toSource mapper)} ->
        Selection mapper
  sel xs = sel (toMapValues xs)

mapRecordM : Monad m =>
             SelectionM m mapper -> Record (toSource mapper) ->
             m (Record (toTarget mapper))
mapRecordM (MkSelection values nubProof) (MkRecord xs _) {mapper} = let
  content = mapRecordM values xs
  targetProof = nubSourceTarget mapper nubProof
  in map (\values' => MkRecord values' targetProof) content

filterMapM : Monad m =>
             SelectionM m mapper -> Record header ->
             {auto prf : Sub (toSource mapper) header} ->
             m (Record (toTarget mapper))
filterMapM statement xs {prf} = mapRecordM statement (project xs)
