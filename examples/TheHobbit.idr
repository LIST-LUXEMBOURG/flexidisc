module TheHobbit

import Flexidisc
import Flexidisc.Validation

Record' : Header String -> Type
Record' = Record String

location : Record' ["city" ::: String, "region" ::: String, "smial" ::: String]
location = [ "region" := "Shire"
           , "city"   := "Hobbiton"
           , "smial"  := "Bag End"
           ]

gandalf : Record' [ "firstname" ::: String
                  , "nickname"  ::: String
                  ]
gandalf = [ "firstname" := "Gandalf" , "nickname"  := "The Grey" ]

magician : Record' [ "firstname" ::: String
                   , "nickname"  ::: String
                   , "class"     ::: String
                   ]
magician = "class" := "Magician" :: gandalf

backToGandalf : Record' [ "firstname" ::: String
                        , "nickname"  ::: String
                        ]
backToGandalf = drop "class" magician

keepArbitrary : Record' [ "class" ::: String ]
keepArbitrary = keep ["class"] magician

theGrey : String
theGrey = gandalf !! "nickname"

gandalfWho : Maybe String
gandalfWho = lookup "lastname" gandalf -- Nothing

bilbo : Record' [ "firstname" ::: String
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

theHobbitFirstnames : List (Record' ["firstname" ::: String])
theHobbitFirstnames = toList theHobbitCharacters

fullname : Record' header ->
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

charactersName : List String
charactersName = foldAll longerFullname theHobbitCharacters

gandalf' : Record' [ "firstname" ::: String
                   , "nickname"  ::: String
                   ]
gandalf' = [ "firstname" := "gandalf" , "nickname"  := "The grey" ]

secureFullname : RecordFunc [ "firstname" ::: String ]
                            [ "lastname"  ::: String
                            , "nickname"  ::: String ]
                            (Validation (List String) String)
secureFullname = Func go
  where
    uppercaseFirst : String -> Validation (List String) String
    uppercaseFirst =
      validateL (\str => "In \"" ++ str ++ "\" each word should start with an uppercase")
                (all (isUpper . strHead) . words)
    go req opt = map unwords $ sequence $ catMaybes
                   [ Just (uppercaseFirst (req !! "firstname"))
                   , map  uppercaseFirst (opt !! "nickname")
                   , map  uppercaseFirst (opt !! "lastname")
                   ]

checkedCharactersName : List (Validation (List String) String)
checkedCharactersName = foldAll secureFullname theHobbitCharacters

errorOnCharachtersName : List (Validation (List String) String)
errorOnCharachtersName = foldAll secureFullname [bilbo, gandalf']

