module CleanRecord.SelectionContent


import Control.Monad.Identity
import CleanRecord.IsNo
import CleanRecord.Label
import CleanRecord.Row
import CleanRecord.Nub
import CleanRecord.RecordContent
import CleanRecord.Relation.Sub

%default total
%access public export

public export
data SelectionContentM : (Type -> Type) -> List (Field label) -> List (Field label) -> Type where
  Nil  : SelectionContentM m [] []
  (::) : (s -> m t) -> SelectionContentM m source target ->
         SelectionContentM m ((k, s) :: source) ((k, t) :: target)

namespace PureSelection

  public export
  data PureSelectionContent : List (Field label) -> List (Field label) -> Type where
    Nil  : PureSelectionContent [] []
    (::) : (s -> t) -> PureSelectionContent source target ->
           PureSelectionContent ((k, s) :: source) ((k, t) :: target)

  SelectionContent : List (Field label) -> List (Field label) -> Type
  SelectionContent = SelectionContentM Identity

  toSelectionContent : PureSelectionContent source target ->
                 SelectionContent source target
  toSelectionContent [] = []
  toSelectionContent (f :: xs) = pure . f :: toSelectionContent xs


public export
mapRecordM : Monad m =>
             (selector : SelectionContentM m source target) ->
             (xs : RecordContent source) ->
             m (RecordContent target)
mapRecordM [] [] = pure []
mapRecordM (f :: fs) (x :: xs) = do
  x' <- f x
  map (x' ::) (mapRecordM fs xs)

public export
mapRecord : (selector : SelectionContent source target) ->
            (xs : RecordContent source) ->
            RecordContent target
mapRecord selector = runIdentity . mapRecordM selector

public export
filterMapM : Monad m =>
          (selector : SelectionContentM m source target) ->
          (xs : RecordContent header) ->
          (prf : Sub source header) ->
          m (RecordContent target)
filterMapM selector xs prf = mapRecordM selector (project xs prf)

public export
filterMap : (selector : SelectionContent source target) ->
         (xs : RecordContent header) ->
         (prf : Sub source header) ->
         RecordContent target
filterMap selector xs = runIdentity . filterMapM selector xs


private
test_selection : SelectionContent [("firstname", String), ("age", Nat)]
                                  [("firstname", Nat), ("age", Maybe Nat)]
test_selection = [ pure . length , pure . (\x => guard (x < 120) *> pure x) ]

private
test_mapRecord : RecordContent [("firstname", Nat), ("age", Maybe Nat)]
test_mapRecord = mapRecord test_selection person
  where
    person = toRecordContent ["firstname" ::= "John", "age" ::= 150]


labelAfterSelect :  SelectionContentM m source target -> Label k source ->
                    Label k target
labelAfterSelect [] lbl = lbl
labelAfterSelect (f :: fs) Here = Here
labelAfterSelect (f :: fs) (There later) = There (labelAfterSelect fs later)

labelBeforeSelect : SelectionContentM m source target -> Label k target ->
                    Label k source
labelBeforeSelect [] lbl = lbl
labelBeforeSelect (f :: fs) Here = Here
labelBeforeSelect (f :: fs) (There later) = There (labelBeforeSelect fs later)


nubWithMappedLabel : DecEq label => {ss : List (Field label)} ->
                     (fs : SelectionContentM m ss ts) -> Not (Label k ss) ->
                     NotLabel k ts
nubWithMappedLabel fs p = notLabelFromEvidence (p . labelBeforeSelect fs)

nubSourceTarget : SelectionContentM m source target -> IsNub source -> IsNub target
nubSourceTarget [] y = y
nubSourceTarget (_ :: fs) (p::prf) =
  nubWithMappedLabel fs (getContra p) :: nubSourceTarget fs prf

namespace NamedContent

  public export
  data ExplicitSelection : (Type -> Type) -> (k : key) -> Type -> Type -> Type where
    MkExplicitSelection : (s -> m t) -> ExplicitSelection m k s t

  public export
  (::=) : (k : key) -> (s -> m t) -> ExplicitSelection m k s t
  (::=) k = MkExplicitSelection

  public export
  data NamedSelectionContentM : (Type -> Type) ->
                                List (Field label) ->
                                List (Field label) ->  Type where
    Nil : NamedSelectionContentM m [] []
    (::) : ExplicitSelection m lbl s t -> NamedSelectionContentM m source target ->
           NamedSelectionContentM m ((lbl, s) :: source) ((lbl, t) :: target)

  toSelectionContent : NamedSelectionContentM m source target ->
                       SelectionContentM m source target
  toSelectionContent [] = []
  toSelectionContent ((MkExplicitSelection f) :: xs) = f :: toSelectionContent xs
