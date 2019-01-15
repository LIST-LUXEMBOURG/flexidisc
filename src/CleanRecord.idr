module CleanRecord

import public CleanRecord.Elem
import public CleanRecord.IsNo
import public CleanRecord.Nub
import public CleanRecord.OrdSub
import public CleanRecord.Sub

import Data.Vect

%default total


public export
Field : (label : Type) -> Type
Field label = Pair label Type

public export
labels : Vect n (label, value) -> Vect n label
labels [] = []
labels (x::xs) = fst x :: labels xs


public export
Header' : (n : Nat) -> (label : Type) -> Type
Header' n label = DPair (Vect n (Field label)) IsNub

public export
Header : DecEq a => (xs : Vect n (Field a)) -> {auto prf : IsNub xs} -> Header' n a
Header xs {prf} = (xs ** prf)

public export
dropHeaderElem : (header : Vect (S n) (Field label)) -> (nubProof : IsNub header) ->
                 (loc : Elem k v header) ->
                 Header' n label
dropHeaderElem header nubProof loc =
  (dropElem header loc ** isNubFromOrdSub (ordSubFromDrop header loc) nubProof)

public export
dropHeaderField : (k : label) ->
                  (header : Vect (S n) (Field label)) ->
                  (nubProof : IsNub header) ->
                  {auto p : Elem k v header} ->
                  Header' n label
dropHeaderField name header nubProof {p} = dropHeaderElem header nubProof p

public export
updateHeaderElem : (header : Vect n (Field label)) ->
                   (nubProof : IsNub header) ->
                   (loc : Elem k v header) ->
                   (new : Type) ->
                   Header' n label
updateHeaderElem header nubProof loc new =
  (updateElem header loc new ** updatePreservesNub nubProof)


public export
updateHeaderField : (k : label) ->
                    (header : Vect n (Field label)) ->
                    (nubProof : IsNub header) ->
                    (new : Type) ->
                    {auto p : Elem k v header} ->
                    Header' n label
updateHeaderField name header nubProof new {p} =
  updateHeaderElem header nubProof p new


export
data Record' : (Header' n label) -> Type where
  Nil : Record' ([] ** [])
  (::) : DecEq label =>
         {l : label} -> {auto newPrf : NotKey l xs} ->
         t -> Record' (xs ** prf) ->
         Record' (((l, t) :: xs) ** (newPrf::prf))

%name Record' rec, xs, ys, zs

export
Record : DecEq label => (h : Vect n (Field label)) -> {auto prf : IsNub h} -> Type
Record xs = Record' (Header xs)

infix 9 :=

public export
(:=) : a -> b -> (a,b)
(:=) = MkPair

t_record1 : Record ["Bar" := Nat]
t_record1 = [42]

t_record2 : Record ["Foo" := String]
t_record2 = ["Test"]

t_record_3 : Record ["Foo" := String, "Bar" := Nat]
t_record_3 = ["Test", 42]

t_record_3' : Record ["Foo" := String, "Bar" := Nat]
t_record_3' = "Test" :: t_record1

export
atElem : (rec : Record' (xs ** prf)) -> (loc : Elem label ty xs) -> ty
atElem (x :: _) Here = x
atElem (_ :: rec) (There later) = atElem rec later

export
get : (field : a) -> (rec : Record' (xs ** prf)) -> {auto p : Elem field ty xs} -> ty
get field rec {p} = atElem rec p

t_get_1 : String
t_get_1 = get "Foo" t_record_3

t_get_2 : Nat
t_get_2 = get "Bar" t_record_3

export
ordSubRecord : Record' (header ** nubProof) ->
               (ordsubPrf : OrdSub sub header) ->
               Record' (sub ** isNubFromOrdSub ordsubPrf nubProof)
ordSubRecord [] Empty = []
ordSubRecord (x :: xs) (Skip sub) = ordSubRecord xs sub
ordSubRecord (x :: xs) (Keep sub) = x :: ordSubRecord xs sub

export
dropElem : {header : Vect (S n) (Field a)} ->
           (rec : Record' (header ** nubProof)) -> (p : Elem k v header) ->
           Record' (dropHeaderElem header nubProof p)
dropElem rec p {header} = ordSubRecord rec (ordSubFromDrop header p)

export
dropField : {header : Vect (S n) (Field a)} ->
            (k : a) -> (rec : Record' (header ** nubProof)) ->
            {auto p : Elem k v header} ->
            Record' (dropHeaderField k header nubProof)
dropField name rec {p} {header} = ordSubRecord rec (ordSubFromDrop header p)

t_drop_1 : Record ["Bar" := Nat]
t_drop_1 = dropElem t_record_3 Here

t_drop_2 : Record ["Bar" := Nat]
t_drop_2 = dropField "Foo" t_record_3

t_drop_3 : Record ["Foo" := String]
t_drop_3 = dropElem t_record_3 (There Here)

t_drop_4 : Record ["Foo" := String]
t_drop_4 = dropField "Bar" t_record_3

export
updateElem : {header : Vect n (Field a)} ->
             (rec : Record' (header ** nubProof)) ->
             (loc : Elem k ty header) -> (ty -> tNew) ->
             Record' (updateHeaderElem header nubProof loc tNew)
updateElem (x :: xs) Here f = f x :: xs
updateElem (x :: xs) (There later) f = x :: updateElem xs later f

export
updateField : {header : Vect n (Field a)} ->
             (k : a) ->
             (ty -> tNew) ->
             (rec : Record' (header ** nubProof)) ->
             {auto p : Elem k ty header} ->
             Record' (updateHeaderField k header nubProof tNew)
updateField k f xs {p} = updateElem xs p f

t_update_1 : Record ["Foo" := Nat, "Bar" := Nat]
t_update_1 = updateElem t_record_3 Here length

t_update_2 : Record ["Foo" := String, "Bar" := String]
t_update_2 = updateField "Bar" (const "BAAAAAR") t_record_3

export
subRecord : Record' (header ** nubProof) ->
            (subPrf : Sub sub header) ->
            Record' (sub ** isNubFromSub subPrf nubProof)
subRecord [] Empty = []
subRecord (x :: rec) (Skip sub) = subRecord rec sub
subRecord rec (Keep e sub) {nubProof = p :: pf} = atElem rec e :: subRecord (dropElem rec e) sub

export
rearrange : Record' (pre ** nubProof) -> {auto prf : Sub post pre} ->
            Record' (post ** isNubFromSub prf nubProof)
rearrange rec {prf} = subRecord rec prf

t_rearrange : Record ["Bar" := Nat, "Foo" := String]
t_rearrange = rearrange t_record_3

export
decKey : DecEq a =>
           {header : Vect n (Field a)} ->
           (k : a) -> (rec : Record' (header ** nubProof)) -> Dec (ty ** Elem k ty header)
decKey k rec {header} = decKey k header
