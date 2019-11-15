||| `Flexidisc` is an implementation of extensible records in Idris.
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
|||   and `Ord` interface.
module Flexidisc

import public Flexidisc.Record
import public Flexidisc.Record.Connection
import public Flexidisc.Record.Transformation
import public Flexidisc.RecordList
