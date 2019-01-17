module CleanRecord.Tutorial

import CleanRecord
import CleanRecord.Instance

person0 : Record ["Firstname" := String]
person0 = ["John"]

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

||| We can of course extend records:
||| we can use either the definition below or `person1 = ["Biri", "Nicolas"]
person1 : Record ["Age" := Nat, "Lastname" := String, "Firstname" := String]
person1 = 42 :: "Doe" :: person0

||| We can also reorder them. Such operation ensure that no-field is loss.
person2 :  Record ["Firstname" := String, "Lastname" := String, "Age" := Nat]
person2 = reorder person1

||| We can also project a record on a smaller and/or reordered one
person3 : Record ["Firstname" := String, "Lastname" := String]
person3 = project person1

||| You can alternatively decide to drop a field by its name:
person4 :  Record ["Firstname" := String, "Lastname" := String]
person4 = dropField "Age" person2

||| Field can be updated quite easily too
olderPerson2 : Record ["Firstname" := String, "Lastname" := String, "Age" := Nat]
olderPerson2 = updateField "Age" (+1) person2

||| What if we want a generic `birthday` function for record with an age?
||| The result type is a bit complex here.
||| Actually we just explain that we update the `"Age"` field, replacing it
||| its content by a Nat.
birthday : Record' (xs ** prf) -> {auto hasAge: Row "Age" Nat xs} ->
           Record' (updateHeaderRow xs prf hasAge Nat)
birthday rec = updateField "Age" (+1) rec

||| And we can check that it works on different types:
olderPeople : ( Record ["Age" := Nat, "Lastname" := String, "Firstname" := String]
              , Record ["Firstname" := String, "Lastname" := String, "Age" := Nat]
              )
olderPeople = (birthday person1, birthday person2)

||| We can also decide to merge records if there is no overlap
twoPartsPerson : Record [ "ID" := Nat
                        , "Firstname" := String
                        , "Lastname" := String
                        , "Age" := Nat
                        ]
twoPartsPerson = merge part1 part2
  where
    part1 : Record ["ID" := Nat, "Firstname" := String]
    part1 = [1, "John"]
    part2 : Record ["Lastname" := String, "Age" := Nat]
    part2 = ["Doe", 42]

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
    part1 = [1, "John"]
    part2 : Record ["ID" := Nat, "Lastname" := String, "Age" := Nat]
    part2 = [1, "Doe", 42]


||| So far, we had provided row names are in the type signature.
||| This solution may look cumbersome on longer records.
||| Moreover, it requires us to provide the values in the exact same order
||| as the one given in the signature.
||| We can do better with `RecordVect`, a intermediate structure that can
||| be used to create records.
||| RecordVect is almost like a Record, but unicity of its fields is not
||| guaranteed
||| `build` enables two things: (1) it ensure fields uniqueness and
||| (2) it reoders the fields to fit the expected Record type
personWithRecordVect : Record [ "ID" := Nat
                              , "Firstname" := String
                              , "Lastname" := String
                              , "Age" := Nat]
personWithRecordVect = build [ "Firstname" ::= "John"
                             , "ID" ::= 0
                             , "Age" ::= 42
                             , "Lastname" ::= "Doe"
                             ]

||| You don't want to reoder the fields or don't care about the order?
||| Use `buildAsIs`, which keep the order used in the declaration,
||| as we do with the two parts in this example:
twoPartsPerson2 : Record [ "ID" := Nat
                        , "Firstname" := String
                        , "Lastname" := String
                        , "Age" := Nat
                        ]
twoPartsPerson2 = merge (buildAsIs ["ID" ::= the Nat 1, "Firstname" ::= "John"])
                        (buildAsIs ["Lastname" ::= "Doe", "Age" ::= the Nat 42])
