module Selection

import CleanRecord
import CleanRecord.Selection

firstnameLengthAndAdult : Selection ["Firstname" := String, "Age" := Nat]
                              ["Firstname" := Nat, "Age" := Maybe Nat]
firstnameLengthAndAdult = sel [length, \x => guard (x >= 18) *> Just x]

person : Record ["Age" := Nat, "Lastname" := String, "Firstname" := String]
person = rec [40, "Doe", "John"]

withNamedSelection : Record ["Firstname" := Nat, "Age" := Maybe Nat]
withNamedSelection = select (namedSel [ "Firstname" ::= length
                                      ,  "Age" ::= \x => guard (x >= 18) *> Just x
                                      ]) person

selectFromLarger : Record ["Firstname" := Nat, "Age" := Maybe Nat]
selectFromLarger = select firstnameLengthAndAdult person
