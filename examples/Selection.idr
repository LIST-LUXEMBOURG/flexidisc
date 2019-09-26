module Selection

import Flexidisc.Record
import Flexidisc.Record.Transformation

person : Record String ["Age" ::: Nat, "Lastname" ::: String, "Firstname" ::: String]
person = ["Age" := 40, "Lastname" := "Doe", "Firstname" := "John"]

justSelection : Maybe (Record String ["Firstname" ::: String, "Lastname" ::: String, "Age" ::: Nat])
justSelection = patchRecord ["Age" := keepIf (>= 18)] person


kid : Record String ["Age" ::: Nat, "Lastname" ::: String, "Firstname" ::: String]
kid = ["Age" := 10, "Lastname" := "Doe", "Firstname" := "John"]

nothingSelection : Maybe (Record String ["Firstname" ::: String, "Lastname" ::: String, "Age" ::: Nat])
nothingSelection = patchRecord ["Age" := keepIf (>= 18)] kid
