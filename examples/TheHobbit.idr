module TheHobbit

import CleanRecord
import CleanRecord.RecordList

location : Record String ["city" ::: String, "region" ::: String, "smial" ::: String]
location = [ "region" := "Shire"
           , "city"   := "Hobbiton"
           , "smial"  := "Bag End"
           ]

gandalf : Record String [ "firstname" ::: String
                        , "nickname"  ::: String
                        ]
gandalf = [ "firstname" := "Gandalf" , "nickname"  := "The Grey" ]

magician : Record String [ "firstname" ::: String
                         , "nickname"  ::: String
                         , "class"     ::: String
                         ]
magician = "class" := "Magician" :: gandalf

backToGandalf : Record String [ "firstname" ::: String
                              , "nickname"  ::: String
                              ]
backToGandalf = drop "class" magician

keepArbitrary : Record String [ "class" ::: String ]
keepArbitrary = keep ["class"] magician

theGrey : String
theGrey = gandalf !! "nickname"

gandalfWho : Maybe String
gandalfWho = lookup "lastname" gandalf -- Nothing

bilbo : Record String [ "firstname" ::: String
                      , "lastname"  ::: String
                      ]
bilbo = [ "firstname" := "Bilbo", "lastname" := "Baggins" ]

theHobbitCharacters : RecordList String
                                 [ [ "firstname" ::: String
                                   , "nickname"  ::: String ]
                                 , [ "firstname" ::: String
                                   , "lastname"  ::: String ]
                                 ]
theHobbitCharacters = [gandalf, bilbo]

theHobbitFirstnames : List (Record String ["firstname" ::: String])
theHobbitFirstnames = toList theHobbitCharacters

fullname : Record String header ->
           {auto fProof : Row "firstname" String header} ->
           {auto lProof : Row "lastname"  String header} ->
           String
fullname xs = unwords [xs !! "firstname", xs !! "lastname"]

longerFullname : RecordFunc [ "firstname" ::: String ]
                            [ "lastname"  ::: String
                            , "nickname"  ::: String ]
                            String
longerFullname = Func go
  where
    go req opt = unwords $ (req !! "firstname")
                         :: catMaybes [ opt !! "nickname"
                                      , opt !! "lastname" ]
