module CleanRecord.IsNo

%default total
%access public export

||| Build at type level the proof that a decidable property is valid
data IsNo : prop -> Type where
  SoFalse : IsNo (No prop)

%name IsNo no, prf, xx, ko

||| Demote an absurd proof from the type level to the value level
getContra : {witness : Dec prop} -> IsNo witness -> (Not prop)
getContra x {witness = (Yes prf)} impossible
getContra x {witness = (No contra)} = contra

||| If I can prove two times that a property doesn't hold,
||| the two proofs are equal
uniqueNo : (prop : Dec any) -> (x : IsNo prop) -> (y : IsNo prop) -> x = y
uniqueNo (Yes _) SoFalse _ impossible
uniqueNo (No contra) SoFalse SoFalse = Refl
