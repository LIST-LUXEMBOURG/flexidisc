module CleanRecord.Instance

import CleanRecord as CR
import Data.Vect as V

%default total

infix 8 ::=
infixr 7 &:

namespace Record

  public export
  data Row : (k : key) -> Type -> Type where
    MkRow : v -> Row k v

  public export
  (::=) : (k : key) -> value -> Row k value
  (::=) k v = MkRow v

  public export
  data RecordVect : Vect n (Field label) -> Type where
    Nil  : RecordVect []
    (::) : Row l v ->
           RecordVect xs ->
           RecordVect ((l, v) :: xs)


t_recordVect : RecordVect ["Foo" := String, "Bar" := Nat]
t_recordVect = ["Foo" ::= "TEST", "Bar" ::=  42]

t_recordVect_2 : RecordVect ["Foo" := String, "Bar" := Nat, "FooBar" := Maybe String]
t_recordVect_2 = ["Foo" ::= "TEST", "Bar" ::=  42, "FooBar" ::= Nothing]



export
build' : RecordVect header -> {auto prf: IsNub header} -> Record' (header ** prf)
build' x {prf = []} = []
build' ((MkRow x) :: y) {prf = (p :: prf)} = x :: build' y

export
build : RecordVect pre ->
        {auto nubProof : IsNub pre} ->
        {auto prf: Permute post pre} ->
        Record' (post ** isNubFromPermute prf nubProof)
build xs = rearrange (build' xs)

t_build : Record ["Name" := String, "Age" := Nat]
t_build = build' ["Name" ::= "John Doe", "Age" ::= 42]

t_build_2 : Record ["Name" := String, "Age" := Nat]
t_build_2 = build ["Age" ::= 42, "Name" ::= "John Doe"]

t_build_3 : Record ["Name" := String, "Age" := Nat, "Marital" := Maybe String]
t_build_3 = build' ["Name" ::= "John Doe", "Age" ::= 42, "Marital" ::= Nothing]

t_build_4 : Record ["Name" := String, "Age" := Nat, "Marital" := Maybe String]
t_build_4 = build ["Age" ::= the Nat 42, "Name" ::= "John Doe", "Marital" ::= Nothing]
