module CleanRecord.SelectionContent

import CleanRecord.IsNo
import CleanRecord.Label
import CleanRecord.Nub
import CleanRecord.RecordContent
import CleanRecord.Relation.Sub

import public Data.Vect

%default total
%access public export

public export
data SelectionContent : Vect n (Field label) -> Vect n (Field label) -> Type where
  Nil  : SelectionContent [] []
  (::) : (s -> t) -> SelectionContent source target ->
         SelectionContent ((k, s) :: source) ((k, t) :: target)

public export
mapRecord : (selector : SelectionContent source target) ->
         (xs : RecordContent source) ->
         RecordContent target
mapRecord [] [] = []
mapRecord (f :: fs) (x :: xs) = f x :: mapRecord fs xs

public export
select : (selector : SelectionContent source target) ->
         (xs : RecordContent header) ->
         (prf : Sub source header) ->
         RecordContent target
select selector xs prf = mapRecord selector (project xs prf)

private
test_selection : SelectionContent [("firstname", String), ("age", Nat)]
                                  [("firstname", Nat), ("age", Maybe Nat)]
test_selection = [ length , (\x => guard (x < 120) *> pure x) ]

private
test_mapRecord : RecordContent [("firstname", Nat), ("age", Maybe Nat)]
test_mapRecord = mapRecord test_selection person
  where
    person = toRecordContent ["firstname" ::= "John", "age" ::= 150]


labelAfterSelect :  SelectionContent source target -> Label k source ->
                    Label k target
labelAfterSelect [] lbl = lbl
labelAfterSelect (f :: fs) Here = Here
labelAfterSelect (f :: fs) (There later) = There (labelAfterSelect fs later)

labelBeforeSelect : SelectionContent source target -> Label k target ->
                    Label k source
labelBeforeSelect [] lbl = lbl
labelBeforeSelect (f :: fs) Here = Here
labelBeforeSelect (f :: fs) (There later) = There (labelBeforeSelect fs later)


nubWithMappedLabel : DecEq label => {ss : Vect n (Field label)} ->
                     (fs : SelectionContent ss ts) -> Not (Label k ss) ->
                     NotLabel k ts
nubWithMappedLabel fs p = notLabelFromEvidence (p . labelBeforeSelect fs)

nubSourceTarget : SelectionContent source target -> IsNub source -> IsNub target
nubSourceTarget [] y = y
nubSourceTarget (_ :: fs) (p::prf) =
  nubWithMappedLabel fs (getContra p) :: nubSourceTarget fs prf

namespace NamedContent

  public export
  data ExplicitSelection : (k : key) -> Type -> Type -> Type where
    MkExplicitSeleciton : (s -> t) -> ExplicitSelection k s t

  public export
  (::=) : (k : key) -> (s -> t) -> ExplicitSelection k s t
  (::=) k = MkExplicitSeleciton

  public export
  data NamedSelectionContent : Vect n (Field label) ->
                               Vect n (Field label) ->  Type where
    Nil : NamedSelectionContent [] []
    (::) : ExplicitSelection lbl s t -> NamedSelectionContent source target ->
           NamedSelectionContent ((lbl, s) :: source) ((lbl, t) :: target)

  toSelectionContent : NamedSelectionContent source target ->
                       SelectionContent source target
  toSelectionContent [] = []
  toSelectionContent ((MkExplicitSeleciton f) :: xs) = f :: toSelectionContent xs
