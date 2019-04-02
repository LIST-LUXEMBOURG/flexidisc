module Flexidisc.Dec.IsYes

%default total

||| Build at type level the proof that a decidable property is valid
public export
data IsYes : prop -> Type where
  SoTrue : IsYes (Yes prop)

%name IsYes yes, prf, ok

||| Demote a proof from the type level to the value level
export
getProof : {witness : Dec prop} -> IsYes witness -> prop
getProof yes {witness = (Yes prf)} = prf
getProof yes {witness = (No contra)} impossible


||| If I can prove two times that a property doesn't hold,
||| the two proofs are equal
export
uniqueYes : (prop : Dec any) -> (x : IsYes prop) -> (y : IsYes prop) -> x = y
uniqueYes (Yes prf) SoTrue SoTrue = Refl
uniqueYes (No _) SoTrue _ impossible
