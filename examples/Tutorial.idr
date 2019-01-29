module CleanRecord.Tutorial

import CleanRecord

person0 : Record ["Firstname" := String]
person0 = rec ["John"]

||| From here, we can access row by name.
|||
||| Fields are verified at compile time: if we try to access a field that is
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
person1 : Record ["Age" := Nat, "Lastname" := String, "Firstname" := String]
person1 = 42 :: "Doe" :: person0

||| We can also reorder them. Such operation ensure that no-field is loss.
person2 :  Record ["Firstname" := String, "Lastname" := String, "Age" := Nat]
person2 = reorder person1

||| We can also project a record on a smaller and/or reordered one
person3 : Record ["Firstname" := String, "Lastname" := String]
person3 = project person1

||| If you want to give explicitly the order of the new elements you want
||| you can use `keep`
person4 : Record ["Firstname" := String, "Lastname" := String]
person4 = keep ["Firstname", "Lastname"] person1

||| If you want to give explicitly the order of the new elements you want
||| you can use `keep`
person4' : Record ["Age" := Nat]
person4' = dropN ["Firstname", "Lastname"] person1

||| You can alternatively decide to drop a field by its name:
person5 :  Record ["Firstname" := String, "Lastname" := String]
person5 = dropByName "Age" person2

||| You can also patch a record with another record
person6 :  Record ["Firstname" := String, "Lastname" := String, "Age" := Nat]
person6 = patch person2 (namedRec ["Lastname" ::= "Biri", "Firstname" ::= "Nicolas"])

||| Field can be updated quite easily too
olderPerson2 : Record ["Firstname" := String, "Lastname" := String, "Age" := Nat]
olderPerson2 = updateByName "Age" (+1) person2

||| What if we want a generic `birthday` function for record with an age?
||| The result type is a bit complex here.
||| Actually we just explain that we update the `"Age"` field, replacing it
||| its content by a Nat.
birthday : Record xs -> {auto hasAge: Row "Age" Nat xs} ->
           Record (updateRow xs hasAge Nat)
birthday rec = updateByName "Age" (+1) rec

||| And we can check that it works on different types:
olderPeople : ( Record ["Age" := Nat, "Lastname" := String, "Firstname" := String]
              , Record ["Firstname" := String, "Lastname" := String, "Age" := Nat]
              )
olderPeople = (birthday person1, birthday person2)

||| You can also ensure that several fields aere presents
fullname : Record xs ->
           {auto requiredFields : Sub [ "Firstname" := String
                                      , "Lastname"  := String ] xs} ->
           String
fullname x = (x !! "Firstname") ++ " " ++ (x !! "Lastname")

||| We can also decide to merge records if there is no overlap
twoPartsPerson : Record [ "ID" := Nat
                        , "Firstname" := String
                        , "Lastname" := String
                        , "Age" := Nat
                        ]
twoPartsPerson = part1 ++ part2
  where
    part1 : Record ["ID" := Nat, "Firstname" := String]
    part1 = rec [1, "John"]
    part2 : Record ["Lastname" := String, "Age" := Nat]
    part2 = rec ["Doe", 42]

||| If there is a duplicate field, you can also use it to decide whether
||| you merge your records or not
twoPartsWithIDPerson : Maybe (Record [ "ID" := Nat
                                     , "Firstname" := String
                                     , "Lastname" := String
                                     , "Age" := Nat
                                     ])
twoPartsWithIDPerson = mergeOn "ID" part1 part2
  where
    part1 : Record ["ID" := Nat, "Firstname" := String]
    part1 = rec [1, "John"]
    part2 : Record ["ID" := Nat, "Lastname" := String, "Age" := Nat]
    part2 = rec [1, "Doe", 42]


||| So far, we had provided row names are in the type signature.
||| This solution may look cumbersome on longer records.
||| Moreover, it requires us to provide the values in the exact same order
||| as the one given in the signature.
||| We can do better with NamedRecordContent,
||| a structure that allows the definition of rows label on the fly.
personWithRecordVect : Record [ "ID" := Nat
                              , "Firstname" := String
                              , "Lastname" := String
                              , "Age" := Nat]
personWithRecordVect = namedRec [ "ID" ::= 0
                                , "Firstname" ::= "John"
                                , "Lastname" ::= "Doe"
                                , "Age" ::= 42
                                ]

||| Its power is probably clearer on the merge example:
twoPartsPersonNamed : Record [ "ID" := Nat
                             , "Firstname" := String
                             , "Lastname" := String
                             , "Age" := Nat
                             ]
twoPartsPersonNamed =
  namedRec ["ID" ::= the Nat 1, "Firstname" ::= "John"] ++
  namedRec ["Lastname" ::= "Doe", "Age" ::= the Nat 42]

||| Equality between `Record` is defined and is order-dependent
|||
||| For example, this wont even compile since both record have different order.
|||
||| ```
||| notEqExample = person1 == person3
||| ```
eqExample : Bool
eqExample = person3 == person4

||| If you want an order-independent equality check, you can either use
||| `reorder` on one of the parameters, to reorder the content of the record,
||| or use `=?=`, which does it for you automatically
eqOrderIndependent : Bool
eqOrderIndependent = person1 =?= person2
