module Selection

import CleanRecord
import CleanRecord.Selection

person : Record ["Age" := Nat, "Lastname" := String, "Firstname" := String]
person = rec [40, "Doe", "John"]

justSelection : Maybe (Record ["Firstname" := String, "Age" := Nat])
justSelection = filterMapM (namedSel [ "Firstname" ::= pure
                                     , "Age" ::= \x => guard (x >= 18) *> Just x
                                     ])
                           person


kid : Record ["Age" := Nat, "Lastname" := String, "Firstname" := String]
kid = rec [10, "Doe", "John"]

nothingSelection : Maybe (Record ["Firstname" := String, "Age" := Nat])
nothingSelection = filterMapM (namedSel [ "Firstname" ::= pure
                                        ,  "Age" ::= \x => guard (x >= 18) *> Just x
                                        ])
                              kid
