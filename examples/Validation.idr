module Example.Validation

import Data.Fin
import Data.String

import Flexidisc
import Flexidisc.Validation

data AcceptedColour = Red | Blue

data Error = CantParseColour String
           | CantParseQuantity String

parseColour : String -> ValidationL Error AcceptedColour
parseColour "red" = Valid Red
parseColour "blue" = Valid Blue
parseColour str = Error $ pure (CantParseColour str)

parseQuantity : String -> ValidationL Error Nat
parseQuantity str = maybe (Error (pure $ CantParseQuantity str))
                          Valid
                          $ parsePositive str

Line : (m : Type -> Type) -> (name : Type) -> (qty : Type) -> Type
Line m name qty = RecordM m String ["colour" ::: name, "qty" ::: qty]

ImportedLine : Type
ImportedLine = Line id String String

ValidatedLine : Type
ValidatedLine = Line id AcceptedColour Nat

validateLine : ImportedLine -> ValidationL Error ValidatedLine
validateLine x = traverseRecord
                   [ "colour" := parseColour
                   , "qty" := parseQuantity
                   ] x

testOK : ValidationL Error ValidatedLine
testOK = validateLine ["colour" := "red", "qty" := "100"]
-- Valid ["name" := Red, "qty" := 100]

testKOColour : ValidationL Error ValidatedLine
testKOColour = validateLine ["colour" := "reed", "qty" := "100"]
-- Error [CantParseColour "reed"]

testKOQty : ValidationL Error ValidatedLine
testKOQty = validateLine ["colour" := "red", "qty" := "-10"]
-- Error [CantParseQuantity "-10"]

testKOBoth : ValidationL Error ValidatedLine
testKOBoth = validateLine ["colour" := "reed", "qty" := "-10"]
-- Error [CantParseColour "reed", CantParseQuantity "-10"]
