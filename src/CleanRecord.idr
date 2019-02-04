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

import public CleanRecord.Elem.Label
import public CleanRecord.Elem.Row

import public CleanRecord.InjectiveDecEq
import public CleanRecord.IsNo
import public CleanRecord.Nub

import public CleanRecord.Record
import public CleanRecord.Record.RecordContent

import public CleanRecord.List.RecordList

import public CleanRecord.Relation.Compliance
import public CleanRecord.Relation.Disjoint
import public CleanRecord.Relation.NegSub
import public CleanRecord.Relation.OrdSub
import public CleanRecord.Relation.Permutation
import public CleanRecord.Relation.SkipSub
import public CleanRecord.Relation.Sub
import public CleanRecord.Relation.SubWithKeys
import public CleanRecord.Relation.Update

import public CleanRecord.Selection
import public CleanRecord.Selection.SelectionContent

%default total
