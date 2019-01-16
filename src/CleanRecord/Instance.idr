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
  data RecordVect' : Header' n label -> Type where
    Nil  : RecordVect' ([] ** [])
    (::) : DecEq label =>
           {l : label} ->
           Row l v ->
           RecordVect' (xs ** prf) ->
           {auto newPrf : NotKey l xs} ->
           RecordVect' (((l, v) :: xs) ** (newPrf::prf))


  inject : DecEq label =>
         {k : label} ->
         Row k v -> Record' (header ** nubPrf) ->
         {auto prf : NotKey k header} ->
         Record' ((k,v)::header ** prf :: nubPrf)
  inject (MkRow x) xs = x :: xs


  (&:) : DecEq label =>
         {k : label} ->
         {auto prf : NotKey k header} ->
         Row k v -> Record' (header ** nubPrf) ->
         Record' ((k,v)::header ** prf :: nubPrf)
  (&:) (MkRow x) xs = x :: xs


public export
RecordVect : DecEq label =>
             (h : Vect n (Field label)) -> {auto prf : IsNub h} -> Type
RecordVect xs = RecordVect' (Header xs)


t_recordVect : RecordVect ["Foo" := String, "Bar" := Nat]
t_recordVect = ["Foo" ::= "TEST", "Bar" ::=  42]

{-
t_recordVect_2 : RecordVect ["Foo" := String, "Bar" := Nat, "FooBar" := Maybe String]
t_recordVect_2 = ["Foo" ::= "TEST", "Bar" ::=  42, "FooBar" ::= Nothing]
-}

t_recordVect_3 : Record ["Foo" := String, "Bar" := Nat, "FooBar" := Maybe String]
t_recordVect_3 = "Foo" ::= "TEST" &: "Bar" ::=  42 &: "FooBar" ::= Nothing &: Nil


export
build' : RecordVect' (header ** prf) -> Record' (header ** prf)
build' [] = []
build' ((MkRow x) :: xs) = x :: build' xs

export
build : RecordVect' (pre ** nubProof) ->
        {auto prf: Permute post pre} ->
        Record' (post ** isNubFromPermute prf nubProof)
build xs = rearrange (build' xs)

t_build : Record ["Name" := String, "Age" := Nat]
t_build = build' ["Name" ::= "John Doe", "Age" ::= 42]

t_build_2 : Record ["Name" := String, "Age" := Nat]
t_build_2 = build ["Age" ::= 42, "Name" ::= "John Doe"]

{-
t_build_3 : Record ["Name" := String, "Age" := Nat, "Marital" := Maybe String]
t_build_3 = build' ["Name" ::= "John Doe", "Age" ::= 42, "Marital" ::= Nothing]
-}
