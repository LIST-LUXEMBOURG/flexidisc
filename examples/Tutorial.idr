module CleanRecord.Tutorial

import Test

person0 : Record String ["Firstname" ::: String]
person0 = ["Firstname" := "John"]

||| From here, we can access row by name.
|||
||| Fields arepublic  verified at compile time: if we try to access a field that is
||| not defined for our record, we obtain a compilation error, not a runtime
||| error.
|||
||| One of the key contribution in CleanRecord is that you can't declare the
||| smae field twice (no, it's not that easy)
||| If we add another field 'Firstname', even with a different type,
||| we'll obtain a compilation error.
person0Name : String
person0Name = get "Firstname" person0

||| or with the infix notation:
person0Name' : String
person0Name' = person0 !! "Firstname"


||| We can of course extend records:
person1 : Record String ["Age" ::: Nat, "Lastname" ::: String, "Firstname" ::: String]
person1 = ("Lastname" := "Doe") :: ("Age" := the Nat 42) :: person0

||| We can also project a record on a smaller one
person3 : Record String ["Firstname" ::: String, "Lastname" ::: String]
person3 = project person1

||| If you want to give explicitly the order of the new elements you want
||| you can use `keep`
person4 : Record String ["Firstname" ::: String, "Lastname" ::: String]
person4 = keep ["Firstname", "Lastname"] person1

||| If you want to give explicitly the order of the new elements you want
||| you can use `keep`
person4' : Record String ["Age" ::: Nat]
person4' = discard ["Firstname", "Lastname"] person1

||| You can alternatively decide to drop a field by its name:
person5 :  Record String ["Firstname" ::: String, "Lastname" ::: String]
person5 = drop "Age" person1

{-
||| You can also patch a record with another record
person6 :  Record String ["Firstname" ::: String, "Lastname" ::: String, "Age" ::: Nat]
person6 = patch person2 (namedRec ["Lastname" := "Biri", "Firstname" := "Nicolas"])
-}


||| Field can be updated quite easily too
olderPerson : Record String ["Firstname" ::: String, "Lastname" ::: String, "Age" ::: Nat]
olderPerson = update "Age" (+1) person1

||| What if we want a generic `birthday` function for record with an age?
||| The result type is a bit complex here.
||| Actually we just explain that we update the `"Age"` field, replacing it
||| its content by a Nat.
birthday : Record String xs -> {auto hasAge: Row "Age" Nat xs} ->
           Record String (changeType xs hasAge Nat)
birthday rec = update "Age" (+1) rec

||| And we can check that it works on different types:
olderPeople : ( Record String ["Age" ::: Nat]
              , Record String ["Firstname" ::: String, "Lastname" ::: String, "Age" ::: Nat]
              )
olderPeople = (birthday person4', birthday person1)


||| You can also ensure that several fields are there
fullname : Record String xs ->
           {auto requiredFields : Sub [ "Lastname"  ::: String
                                      , "Firstname" ::: String ] xs} ->
           String
fullname xs = (xs !! "Firstname") ++ " " ++ (xs !! "Lastname")

||| Or ensure that some row doesn't exist to create them
addFullname : Record String (H xs) ->
              {auto requiredFields : Sub [ "Firstname" ::: String
                                         , "Lastname"  ::: String ] (H xs)} ->
              {auto newFields : Disjoint [ "Fullname"  ::: String ] xs} ->
              Record String (H (merge ["Fullname" :::  String] xs))
addFullname r = ["Fullname" := fullname r] ++ r

||| We can also decide to merge records if there is no overlap
twoPartsPerson : Record String [ "ID" ::: Nat
                        , "Firstname" ::: String
                        , "Lastname" ::: String
                        , "Age" ::: Nat
                        ]
twoPartsPerson = ["ID" := the Nat 1, "Firstname" := "John"] ++ ["Lastname" := "Doe", "Age" := the Nat 42]

eqExample : Bool
eqExample = person1 == olderPerson
