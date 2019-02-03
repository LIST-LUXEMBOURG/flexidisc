||| `CleanRecord` is an implementation of extensible records in Idris.
|||
||| It's goal is to provide easy to write extensible record functions that
||| ensure the following:
|||
||| - **Type safety:** operation on row and access to row data is type safe.
||| - **Compile time validation:** row existence and unicity of row
|||   declarations are checked at compile time.
||| - **Lean syntax:** Take advantage of the list syntax as much as possible,
|||   minimize the type declarations as well.
||| - **Custom keys:** Row labels can be any type that implements the `DecEq`
|||   interface.
module CleanRecord

import public CleanRecord.IsNo
import public CleanRecord.Nub
import public CleanRecord.RecordContent
import public CleanRecord.Label
import public CleanRecord.Row

import public CleanRecord.Relation.Compliance
import public CleanRecord.Relation.Disjoint
import public CleanRecord.Relation.NegSub
import public CleanRecord.Relation.OrdSub
import public CleanRecord.Relation.Permutation
import public CleanRecord.Relation.SkipSub
import public CleanRecord.Relation.Sub
import public CleanRecord.Relation.SubWithKeys
import public CleanRecord.Relation.Update

%default total

||| A `Record` is a set of rows
||| @ header The list of rows into the record, with their types
public export
data Record : (header : List (Field label)) -> Type where
  MkRecord : (values : RecordContent header) -> (nubProof : IsNub header) ->
             Record header

||| Build a `Record` from a list of values, the function checks unicity of
||| the fields and build the `Record` if such proof can be generated
export
rec : (xs : RecordContent header) -> {auto nubProof : IsNub header} ->
      Record header
rec xs {nubProof} = MkRecord xs nubProof

||| Build a `Record` from a list of named values (rows). This version is
||| an alternative to `rec` that allows to gdet rid of the `Record` signature.
export
namedRec : (xs : NamedRecordContent header) -> {auto nubProof : IsNub header} ->
      Record header
namedRec xs {nubProof} = MkRecord (toRecordContent xs) nubProof

||| Prepend a value to a record, the label name is given by the result type.
export
cons : DecEq label =>
         {lbl : label} ->
         ty ->
         Record header ->
         {auto fresh : NotLabel lbl header} ->
         Record ((lbl, ty) :: header)
cons x (MkRecord xs prf) {fresh} = MkRecord (x::xs) (fresh::prf)

||| (Almost) infix alias for `cons`
export
(::) : DecEq label =>
         {lbl : label} ->
         ty -> Record header ->
         {auto fresh : NotLabel lbl header} ->
        Record ((lbl, ty) :: header)
(::) x (MkRecord xs prf) {fresh} = MkRecord (x::xs) (fresh::prf)

infixr 7 :+:

||| Prepend a named value to a record.
export
consRow : DecEq label =>
         {lbl : label} ->
         (Row lbl ty) ->
         Record header ->
         {auto fresh : NotLabel lbl header} ->
        Record ((lbl, ty) :: header)
consRow (MkRow x) (MkRecord xs prf) {fresh} = MkRecord (x::xs) (fresh::prf)


||| (Almost) infix alias for `consRow`
export
(:+:) : DecEq label =>
         {lbl : label} ->
         (Row lbl ty) ->
         Record header ->
         {auto fresh : NotLabel lbl header} ->
        Record ((lbl, ty) :: header)
(:+:) (MkRow x) (MkRecord xs prf) {fresh} = MkRecord (x::xs) (fresh::prf)


infix 9 :=

||| An alias for `MkPair`, that provides a clearer representation of the
||| row types.
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

||| Get value from a Row
atRow : (xs : Record header) -> (Row field ty header) -> ty
atRow (MkRecord xs nubProof) row = atRow xs row

||| Typesafe extraction of a value from a record
|||
||| Complexity is _O(n)_
export
get : (field : a) -> (rec : Record xs) -> {auto p : Row field ty xs} -> ty
get field (MkRecord xs _) {p} = atRow xs p

||| Typesafe extraction of a value from a record,
||| `Nothing` if the Row doesn't exist.
|||
||| Complexity is _O(n)_
export
lookup : DecEq a =>
         (field : a) -> (rec : Record xs) ->
         {auto p : Compliance xs [field := ty]} -> Maybe ty
lookup field rec {p} = case p of
                            (Skip x y) => Nothing
                            (Keep loc x) => Just (get field rec)


infixl 7 !!

||| (Alomost) infix alias for `get`
export
(!!) : (rec : Record xs) -> (field : a) -> {auto p : Row field ty xs} -> ty
(!!) rec field = get field rec

t_get_1 : String
t_get_1 = get "Foo" t_record_3

t_get_2 : Nat
t_get_2 = get "Bar" t_record_3

||| project a part of a `Record`, preserving the order of the fields
|||
||| Complexity is _O(n)_ where _n_ is the initial record size
|||
||| the final record size.
export
ordSub : Record header -> (ordSubPrf : OrdSub sub header) ->
         Record sub
ordSub (MkRecord xs prf) ordSubPrf =
  MkRecord (ordSub xs ordSubPrf) (isNubFromOrdSub ordSubPrf prf)

||| Remove a row from a Record.
|||
||| Complexity is _O(n)_
|||
||| @ xs the record
||| @ p  the proof that the row is in it
export
dropByLabel : {header : List (Field a)} ->
          (xs : Record header) -> (p : Label k header) ->
          Record (dropLabel header p)
dropByLabel xs p {header} = ordSub xs (ordSubFromDrop header p)

||| Remove a row from a Record.
|||
||| Complexity is _O(n)_
|||
||| @ k  the row name
||| @ xs the record
||| @ p  the proof that the row is in it
export
dropByName : {header : List (Field a)} ->
             (k : a) -> (xs : Record header) ->
             {auto p : Label k header} ->
             Record (dropLabel header p)
dropByName name rec {p} {header} = ordSub rec (ordSubFromDrop header p)

t_drop_1 : Record ["Bar" := Nat]
t_drop_1 = dropByLabel t_record_3 Here

t_drop_2 : Record ["Bar" := Nat]
t_drop_2 = dropByName "Foo" t_record_3

t_drop_3 : Record ["Foo" := String]
t_drop_3 = dropByLabel t_record_3 (There Here)

t_drop_4 : Record ["Foo" := String]
t_drop_4 = dropByName "Bar" t_record_3

||| Update a row, the update can change the row type.
|||
||| Complexity is _O(n)_
|||
||| @ xs  the record
||| @ loc the proof that the row is in it
||| @ f   the update function
export
updateRow : {header : List (Field a)} ->
            (xs : Record header) ->
            (loc : Row k ty header) -> (f : ty -> tNew) ->
            Record (updateRow header loc tNew)
updateRow (MkRecord xs prf) loc f {header} =
  MkRecord (updateRow xs loc f) (updatePreservesNub prf)



||| Update a row, the update can change the row type.
|||
||| Complexity is _O(n)_
|||
||| @ k  the row name
||| @ xs  the record
||| @ loc the proof that the row is in it
||| @ f   the update function
export
updateByName : {header : List (Field a)} ->
               (k : a) ->
               (f : ty -> tNew) ->
               (xs : Record header) ->
               {auto loc : Row k ty header} ->
               Record (updateRow header loc tNew)
updateByName k f xs {loc} = updateRow xs loc f

t_update_1 : Record ["Foo" := Nat, "Bar" := Nat]
t_update_1 = updateRow t_record_3 Here length

t_update_2 : Record ["Foo" := String, "Bar" := String]
t_update_2 = updateByName "Bar" (const "BAAAAAR") t_record_3

||| Replace a row, with a new value (it can change the type)
|||
||| Complexity is _O(n)_
|||
||| @ xs  the record
||| @ loc the proof that the row is in it
||| @ new   the new value for the row
export
replaceRow : {header : List (Field a)} ->
            (xs : Record header) ->
            (loc : Label k header) -> (new : tNew) ->
            Record (updateLabel header loc tNew)
replaceRow (MkRecord xs prf) loc new =
  MkRecord (replaceRow xs loc new) (updatePreservesNub prf)

||| Update a row, the update can change the row type.
|||
||| Complexity is _O(n)_
|||
||| @ k  the row name
||| @ xs  the record
||| @ loc the proof that the row is in it
||| @ new   the new value for the row
export
replaceByName : {header : List (Field a)} ->
                (k : a) ->
                (new : tNew) ->
                (xs : Record header) ->
                {auto loc : Label k header} ->
                Record (updateLabel header loc tNew)
replaceByName k new xs {loc} = replaceRow xs loc new

||| Traverse a record with a function
export
traverseByName : Functor f =>
                 {header : List (Field a)} ->
                 (k : a) ->
                 (func : ty -> f tNew) ->
                 (xs : Record header) ->
                 {auto loc : Row k ty header} ->
                 f (Record (updateRow header loc tNew))
traverseByName k func xs = let
  fx = func (xs !! k)
  in map (\x => replaceByName k x xs) fx

||| Like project, but with an explicit proof that the final
||| set of rows is a subset of the initial set.
|||
||| Complexity is _O(mxn)_ where _m_ is the initial record size and _n_
||| the target size
|||
export
project' : Record header ->
           (subPrf : Sub sub header) ->
           Record sub
project' (MkRecord xs prf) subPrf =
  MkRecord (project xs subPrf) (isNubFromSub subPrf prf)

||| Project a record (keep only a subset of its field and reorder them.
|||
||| Complexity is _O(mxn)_ where _m_ is the initial record size and _n_
||| the target size
|||
export
project : Record pre -> {auto prf : Sub post pre} ->
          Record post
project rec {prf} = project' rec prf

t_sub_1 : Record ["Bar" := Nat, "Foo" := String]
t_sub_1 = project t_record_4

t_sub_2 : Record ["Bar" := Nat, "Foo" := String]
t_sub_2 = project t_record_3

||| Like project, but with an explicit proof that the final
||| set of rows is a subset of the initial set.
|||
||| Complexity is _O(mxn)_ where _m_ is the initial record size and _n_
||| the target size
|||
negProject' : Record header ->
           (negPrf : NegSub sub header) ->
           Record sub
negProject' (MkRecord xs prf) subPrf =
  MkRecord (negProject xs subPrf) (isNubFromNegSub subPrf prf)

||| Build a projection with the given keys
|||
||| Complexity is _O(mxn)_ where _m_ is the initial record size and _n_
||| the target size
|||
||| @keys The rows to keep
||| @xs The record to project
||| @prf Proof that the rows are parts of the record
export
keep : (keys : List a) -> (xs : Record pre) ->
       {auto prf : SubWithKeys keys post pre} ->
       Record post
keep _ xs {prf} = project' xs (toSub prf)

||| Build a projection that excludes the given keys
|||
||| Complexity is _O(mxn)_ where _m_ is the initial record size and _n_
||| the target size
|||
||| @keys The rows to skip
||| @xs The record to project
||| @prf Proof that the rows are parts of the record
export
dropN : (keys : List a) -> (xs : Record pre) ->
        {auto prf : SkipSub keys post pre} ->
        Record post
dropN _ xs {prf} = negProject' xs (toNegSub prf)

export
reorder' : Record header -> (permPrf : Permute sub header) ->
           Record sub
reorder' (MkRecord xs prf) permPrf =
  MkRecord (reorder xs permPrf) (isNubFromPermute permPrf prf)

||| Change the order of the rows. It's used intensively to make
||| records "order independent".
|||
||| Complexity is _O(n^2)_ where _n_ is the record size
|||
export
reorder : Record pre -> {auto prf : Permute post pre} ->
          Record post
reorder rec {prf} = reorder' rec prf

t_reorder_1 : Record ["Bar" := Nat, "Foo" := String]
t_reorder_1 = reorder t_record_3

||| Append two records, it fails if some fields are duplicated
|||
||| Complexity is _O(n)_ where _n_ is the length of the first record.
|||
export
merge : DecEq label =>
        {left : List (Field label)} ->
        Record left -> Record right ->
        {auto prf : Disjoint left right} ->
        Record (left ++ right)
merge (MkRecord xs leftNub) (MkRecord ys rightNub) {left} {right} {prf} =
  MkRecord (xs ++ ys) (disjointNub left leftNub right rightNub prf)

||| An infix alias for merge
export
(++) : DecEq label =>
        {left : List (Field label)} ->
        Record left -> Record right ->
        {auto prf : Disjoint left right} ->
        Record (left ++ right)
(++) = merge

t_merge : Record ["Foo" := Nat] -> Record ["Bar" := String] ->
          Record ["Foo" := Nat, "Bar" := String]
t_merge x y = x ++ y

||| Merge data only if the given row has the same value in both records
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
  in guard (l == r) *> pure (merge left (dropByName k right))

||| Patch a record with hte values of another record
export
patch : Record pre -> Record update -> {auto prf : Patch update pre post} ->
        Record post
patch (MkRecord xs nubProof) (MkRecord ys _) {prf} =
  MkRecord (patch xs ys prf) (patchPreservesNub nubProof prf)

||| Decide whether a key is defined in a record or not
export
decLabel : DecEq a =>
         (k : a) -> (rec : Record header) -> Dec (ty ** Row k ty header)
decLabel k rec {header} = decKey k header


||| Check equality between records that have the same set of
||| rows, in the same orders
export
implementation Eqs ts => Eq (Record ts) where
  (==) (MkRecord xs _) (MkRecord ys _) = xs == ys

infix 6 =?=
infix 6 =<?
infix 6 ?>=

||| Order independent comparison.
export
(=?=) : Eqs ts =>
       (xs : Record ts) -> (ys : Record ts') ->
       {auto perm : Permute ts ts'} ->
       Bool
(=?=) xs ys = xs == reorder ys

||| Check that a Record is a subset of another record
export
(=<?) : Eqs ts =>
       (xs : Record ts) -> (ys : Record ts') ->
       {auto perm : Sub ts ts'} ->
       Bool
(=<?) xs ys = xs == project ys

||| Check that a Record is a subset of another record
export
(?>=) : Eqs ts' =>
       (xs : Record ts) -> (ys : Record ts') ->
       {auto perm : Sub ts' ts} ->
       Bool
(?>=) xs ys = project xs == ys

export
implementation Shows key header => Show (Record header) where
  show (MkRecord xs _) = show xs
