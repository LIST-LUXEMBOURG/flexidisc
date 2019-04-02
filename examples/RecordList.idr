module RecordList

import Flexidisc.Record
import Flexidisc.Record.Transformation
import Flexidisc.RecordList

||| `RecordList` are Heterogeneous lists of record
people : RecordList String [ [ "firstname" ::: String
                             , "lastname"  ::: String
                             , "age"       ::: Nat
                             , "location"  ::: Maybe String
                             ]
                           , [ "firstname" ::: String
                             , "location"  ::: String
                             ]
                           ]
people = [ [ "firstname" := "John"
           , "lastname"  := "Doe"
           , "age"       := 42
           , "location"  := Nothing
           ]
         , [ "firstname" := "Waldo"
           , "location" := "Hidden"
           ]
         ]

||| We can find the first record that match the partial information we provide
whereIsWaldo : Maybe (header ** Record String header)
whereIsWaldo = firstWith ["firstname" := is "Waldo"] people


whereIsDoe : Maybe (header ** Record String header)
whereIsDoe = firstWith ["lastname" := is "Doe"] people

||| You can even search for something that is not available in every record
whoIs42 : Maybe (header ** Record String header)
whoIs42 = firstWith ["age" := is (the Nat 42)] people


-- with one limitation, if you look for a specific row,
-- it should have the same type in every rows where it's defined
--
-- this would fail:
--
-- whoIsHidden : Maybe (header ** Record String header)
-- whoIsHidden = firstWith ["location" := is "Hidden"] people
