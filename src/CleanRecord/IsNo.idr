module CleanRecord.IsNo

%default total

||| Build at type level the proof that a decidable property is valid
public export
data IsNo : prop -> Type where
  SoFalse : IsNo (No prop)

||| Demote an absurd proof from the type level to the value level
public export
getContra : {witness : Dec prop} -> IsNo witness -> (Not prop)
getContra x {witness = (Yes prf)} impossible
getContra x {witness = (No contra)} = contra
