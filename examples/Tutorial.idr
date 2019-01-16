module CleanRecord.Tutorial

import CleanRecord
import CleanRecord.Instance

||| Let start with a basic record made of just a firstname.
||| At this stage, we'll be lazy and just use String as labels for our rows.
||| The values can be declared just like an heterogeneous list of values
|||
||| Of course, an invalid type for '"Firstname"' would lead to a compilation
||| error, just like a traditional type.
person0 : Record ["Firstname" := String]
person0 = ["John"]

||| From here, we can access row by name.
|||
||| Fields are verified at compile time: if we try to access a field that is
||| not defined for our record, we obtain a compilation error, not a runtime
||| error.
person0Name : String
person0Name = get "Firstname" person0

||| We can of course extend records:
||| we can use either the definition below or `person1 = ["Biri", "Nicolas"]
person1 : Record ["Age" := Nat, "Lastname" := String, "Firstname" := String]
person1 = 42 :: "Doe" :: person0

||| We can also reorder them. Such operation ensure that no-field is loss.
person2 :  Record ["Firstname" := String, "Lastname" := String, "Age" := Nat]
person2 = rearrange person1

||| We can also reorder and weaken a record
person3 : Record ["Firstname" := String, "Lastname" := String]
person3 = sub person1

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
