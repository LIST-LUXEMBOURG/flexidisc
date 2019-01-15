module CleanRecord.Instance

import CleanRecord as CR
import Data.Vect as V

%default total

namespace Record

  public export
  data Row : (k : key) -> Type -> Type where
    MkRow : v -> Row k v

  infix 9 ::=

  public export
  (::=) : (k : key) -> value -> Row k value
  (::=) k v = MkRow v

  public export
  data RecordVect' : Header' n label -> Type where
    Nil  : RecordVect' ([] ** [])
    (::) : DecEq label =>
           {l : label} ->
           Row l v ->
           RecordVect' (xs ** prf) ->
           {auto newPrf : NotKey l xs} ->
           RecordVect' (((l, v) :: xs) ** (newPrf::prf))

public export
RecordVect : DecEq label =>
             (h : Vect n (Field label)) -> {auto prf : IsNub h} -> Type
RecordVect xs = RecordVect' (Header xs)


t_recordVect : RecordVect ["Foo" := String, "Bar" := Nat]
t_recordVect = ["Foo" ::= "TEST", "Bar" ::=  42]


export
build' : RecordVect' (header ** prf) -> Record' (header ** prf)
build' [] = []
build' ((MkRow x) :: xs) = x :: build' xs

export
build : RecordVect' (pre ** nubProof) ->
        {auto prf: Sub post pre} -> Record' (post ** isNubFromSub prf nubProof)
build xs = rearrange (build' xs)

t_build : Record ["Name" := String, "Age" := Nat]
t_build = build' ["Name" ::= "John Doe", "Age" ::= 42]


t_build_2 : Record ["Name" := String, "Age" := Nat]
t_build_2 = build ["Age" ::= 42, "Name" ::= "John Doe"]
