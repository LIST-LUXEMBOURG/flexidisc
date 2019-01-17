module CleanRecord

import public CleanRecord.Disjoint
import public CleanRecord.Row
import public CleanRecord.IsNo
import public CleanRecord.Nub
import public CleanRecord.OrdSub
import public CleanRecord.Permutation
import public CleanRecord.RecordContent
import public CleanRecord.Sub

import public Data.Vect

%default total

public export
record Record (header : Vect n (Field label)) where
  constructor MkRecord
  values   : RecordContent header
  nubProof : IsNub header


public export
labels : Vect n (label, value) -> Vect n label
labels [] = []
labels (x::xs) = fst x :: labels xs

export
rec : (xs : RecordContent header) -> {auto nubProof : IsNub header} ->
      Record header
rec xs {nubProof} = MkRecord xs nubProof

export
namedRec : (xs : NamedRecordContent header) -> {auto nubProof : IsNub header} ->
      Record header
namedRec xs {nubProof} = MkRecord (toRecordContent xs) nubProof

export
(::) : DecEq label =>
         {lbl : label} ->
         {auto fresh : NotKey lbl header} ->
         ty -> Record header ->
        Record ((lbl, ty) :: header)
(::) x (MkRecord xs prf) {fresh} = MkRecord (x::xs) (fresh::prf)


infix 9 :=

public export
(:=) : a -> b -> (a,b)
(:=) = MkPair

t_record1 : Record ["Bar" := Nat]
t_record1 = rec [42]

t_record2 : Record ["Foo" := String]
t_record2 = rec ["Test"]

t_record_3 : Record ["Foo" := String, "Bar" := Nat]
t_record_3 = rec ["Test", 42]

t_record_3' : Record ["Foo" := String, "Bar" := Nat]
t_record_3' = "Test" :: t_record1

t_record_4 : Record ["Foobar" := Maybe String, "Foo" := String, "Bar" := Nat]
t_record_4 = Just "Test2" :: t_record_3

t_record_4' : Record ["Foobar" := Maybe String, "Foo" := String, "Bar" := Nat]
t_record_4' = rec [Nothing, "Test", 19]

export
lookup : (field : a) -> (rec : Record xs) -> {auto p : Row field ty xs} -> ty
lookup field (MkRecord xs _) {p} = atRow xs p

export
get : (field : a) -> (rec : Record xs) -> {auto p : Row field ty xs} -> ty
get = lookup

infixl 7 !!

export
(!!) : (rec : Record xs) -> (field : a) -> {auto p : Row field ty xs} -> ty
(!!) rec field = get field rec

t_get_1 : String
t_get_1 = get "Foo" t_record_3

t_get_2 : Nat
t_get_2 = get "Bar" t_record_3

export
ordSub : Record header -> (ordSubPrf : OrdSub sub header) ->
         Record sub
ordSub (MkRecord xs prf) ordSubPrf =
  MkRecord (ordSub xs ordSubPrf) (isNubFromOrdSub ordSubPrf prf)

export
dropRow : {header : Vect (S n) (Field a)} ->
          (xs : Record header) -> (p : Row k v header) ->
          Record (dropRow header p)
dropRow xs p {header} = ordSub xs (ordSubFromDrop header p)

export
dropField : {header : Vect (S n) (Field a)} ->
            (k : a) -> (xs : Record header) ->
            {auto p : Row k v header} ->
            Record (dropRow header p)
dropField name rec {p} {header} = ordSub rec (ordSubFromDrop header p)

t_drop_1 : Record ["Bar" := Nat]
t_drop_1 = dropRow t_record_3 Here

t_drop_2 : Record ["Bar" := Nat]
t_drop_2 = dropField "Foo" t_record_3

t_drop_3 : Record ["Foo" := String]
t_drop_3 = dropRow t_record_3 (There Here)

t_drop_4 : Record ["Foo" := String]
t_drop_4 = dropField "Bar" t_record_3

export
updateRow : {header : Vect n (Field a)} ->
            (xs : Record header) ->
            (loc : Row k ty header) -> (ty -> tNew) ->
            Record (updateRow header loc tNew)
updateRow (MkRecord xs prf) loc f {header} =
  MkRecord (updateRow xs loc f) (updatePreservesNub prf)

export
updateField : {header : Vect n (Field a)} ->
             (k : a) ->
             (ty -> tNew) ->
             (rec : Record header) ->
             {auto loc : Row k ty header} ->
             Record (updateRow header loc tNew)
updateField k f xs {loc} = updateRow xs loc f

t_update_1 : Record ["Foo" := Nat, "Bar" := Nat]
t_update_1 = updateRow t_record_3 Here length

t_update_2 : Record ["Foo" := String, "Bar" := String]
t_update_2 = updateField "Bar" (const "BAAAAAR") t_record_3

export
project' : Record header ->
           (subPrf : Sub sub header) ->
           Record sub
project' (MkRecord xs prf) subPrf =
  MkRecord (project xs subPrf) (isNubFromSub subPrf prf)

export
project : Record pre -> {auto prf : Sub post pre} ->
          Record post
project rec {prf} = project' rec prf

t_sub_1 : Record ["Bar" := Nat, "Foo" := String]
t_sub_1 = project t_record_4

t_sub_2 : Record ["Bar" := Nat, "Foo" := String]
t_sub_2 = project t_record_3

export
reorder' : Record header -> (permPrf : Permute sub header) ->
           Record sub
reorder' (MkRecord xs prf) permPrf =
  MkRecord (reorder xs permPrf) (isNubFromPermute permPrf prf)

export
reorder : Record pre -> {auto prf : Permute post pre} ->
          Record post
reorder rec {prf} = reorder' rec prf

t_reorder_1 : Record ["Bar" := Nat, "Foo" := String]
t_reorder_1 = reorder t_record_3


export
merge : DecEq label =>
        {left : Vect n (Field label)} ->
        Record left -> Record right ->
        {auto prf : Disjoint left right} ->
        Record (left ++ right)
merge (MkRecord xs leftNub) (MkRecord ys rightNub) {left} {right} {prf} =
  MkRecord (xs ++ ys) (disjointNub left leftNub right rightNub prf)

t_merge : Record ["Foo" := Nat] -> Record ["Bar" := String] ->
          Record ["Foo" := Nat, "Bar" := String]
t_merge x y = merge x y

export
mergeOn : (DecEq label, Eq ty) =>
          (k : label) ->
          Record left  ->
          Record right ->
          {auto leftLoc  : Row k ty left}  ->
          {auto rightLoc : Row k ty right} ->
          {auto prf : Disjoint left (dropRow right rightLoc)} ->
          Maybe (Record (left ++ dropRow right rightLoc))
mergeOn k left right = let
  l = get k left
  r = get k right
  in guard (l == r) *> pure (merge left (dropField k right))


export
decKey : DecEq a =>
         (k : a) -> (rec : Record header) -> Dec (ty ** Row k ty header)
decKey k rec {header} = decKey k header
