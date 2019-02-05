module CleanRecord.SelectionContent


import CleanRecord.Elem.Label
import CleanRecord.Elem.Row

import CleanRecord.IsNo
import CleanRecord.Nub
import CleanRecord.Record.RecordContent

import CleanRecord.Relation.NegSub
import CleanRecord.Relation.Sub

import Control.Monad.Identity

%default total
%access export

public export
data MapValue label = MkMapValue label Type Type

infixr 8 :->
infix 6  :=

public export
(:->) : Type -> Type -> (label -> MapValue label)
(:->) s t l = MkMapValue l s t

public export
(:=) : label -> (label -> MapValue label) -> MapValue label
(:=) = flip apply


public export
data MapValuesM : (m : Type -> Type) ->List (MapValue label) -> Type where
    Nil  : MapValuesM m []
    (::) : (s -> m t) -> MapValuesM m mapper ->
           MapValuesM m (MkMapValue k s t :: mapper)

public export
MapValues : List (MapValue label) -> Type
MapValues = MapValuesM Identity

public export
toSource : List (MapValue label) -> List (Field label)
toSource [] = []
toSource ((MkMapValue k s t) :: xs) = (k, s) :: toSource xs

public export
toTarget : List (MapValue label) -> List (Field label)
toTarget [] = []
toTarget ((MkMapValue k s t) :: xs) = (k, t) :: toTarget xs


public export
mapRecordM : Monad m =>
             (selector : MapValuesM m mapper) ->
             (xs : RecordContent (toSource mapper)) ->
             m (RecordContent (toTarget mapper))
mapRecordM [] [] = pure []
mapRecordM (f :: fs) (x :: xs) = do
  x' <- f x
  map (x' ::) (mapRecordM fs xs)

public export
mapRecord : (selector : MapValues mapper) ->
            (xs : RecordContent (toSource mapper)) ->
            RecordContent (toTarget mapper)
mapRecord selector = runIdentity . mapRecordM selector


public export
filterMapM : Monad m =>
          (selector : MapValuesM m mapper) ->
          (xs : RecordContent header) ->
          {auto prf : Sub (toSource mapper) header} ->
          m (RecordContent (toTarget mapper))
filterMapM selector xs {prf} = mapRecordM selector (project xs prf)

public export
filterMap : (selector : MapValues mapper) ->
            (xs : RecordContent header) ->
            {auto prf : Sub (toSource mapper) header} ->
            RecordContent (toTarget mapper)
filterMap selector xs = runIdentity $ filterMapM selector xs



namespace PureMapValues

  public export
  data PureMapValues : List (MapValue label) -> Type where
    Nil  : PureMapValues []
    (::) : (s -> t) -> PureMapValues mapper ->
           PureMapValues (MkMapValue k s t :: mapper)

  toMapValues : PureMapValues mapper -> MapValues mapper
  toMapValues [] = []
  toMapValues (f :: xs) = pure . f :: toMapValues xs


labelAfterSelect : (mapper : List (MapValue label)) -> Label k (toSource mapper) ->
                   Label k (toTarget mapper)
labelAfterSelect [] lbl = lbl
labelAfterSelect (MkMapValue k s t :: _) Here = Here
labelAfterSelect (MkMapValue k s t :: fs) (There later) =
  There (labelAfterSelect fs later)

labelBeforeSelect : (mapper : List (MapValue label)) -> Label k (toTarget mapper) ->
                    Label k (toSource mapper)
labelBeforeSelect [] lbl = lbl
labelBeforeSelect (MkMapValue k s t :: fs) Here = Here
labelBeforeSelect (MkMapValue k s t :: fs) (There later) =
  There (labelBeforeSelect fs later)

nubWithMappedLabel : DecEq label => (mapper : List (MapValue label)) ->
                     Not (Label k (toSource mapper)) ->
                     NotLabel k (toTarget mapper)
nubWithMappedLabel fs p = notLabelFromEvidence (p . labelBeforeSelect fs)

%hint
nubSourceTarget : (mapper : List (MapValue label)) -> IsNub (toSource mapper) ->
                  IsNub (toTarget mapper)
nubSourceTarget [] prf = prf
nubSourceTarget (MkMapValue k s t :: fs) (p::prf) =
  nubWithMappedLabel fs (getContra p) :: nubSourceTarget fs prf

namespace NamedContent

  public export
  data NamedMapValue : (Type -> Type) -> (k : key) -> Type -> Type -> Type where
    MkNamedMapValue : (s -> m t) -> NamedMapValue m k s t

  public export
  (::=) : (k : key) -> (s -> m t) -> NamedMapValue m k s t
  (::=) k = MkNamedMapValue

  public export
  data NamedMapValuesM : (Type -> Type) -> List (MapValue label) ->
                         Type where
    Nil : NamedMapValuesM m []
    (::) : NamedMapValue m lbl s t -> NamedMapValuesM m mapped ->
           NamedMapValuesM m (MkMapValue lbl s t :: mapped)

  toMapValuesM : NamedMapValuesM m mapped -> MapValuesM m mapped
  toMapValuesM [] = []
  toMapValuesM ((MkNamedMapValue f) :: xs) = f :: toMapValuesM xs

private
test_selection : MapValues [ "firstname" :=  String :-> Nat , "age" := Nat :-> Maybe Nat ]
test_selection = [ pure . length , pure . (\x => guard (x < 120) *> pure x) ]

private
test_mapRecord : RecordContent [("firstname", Nat), ("age", Maybe Nat)]
test_mapRecord = mapRecord test_selection person
  where
    person = toRecordContent ["firstname" ::= "John", "age" ::= 150]


