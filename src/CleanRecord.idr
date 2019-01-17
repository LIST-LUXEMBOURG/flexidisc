module CleanRecord

import public CleanRecord.Disjoint
import public CleanRecord.Row
import public CleanRecord.IsNo
import public CleanRecord.Nub
import public CleanRecord.OrdSub
import public CleanRecord.Permutation
import public CleanRecord.Sub

import public Data.Vect

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
dropHeaderRow : (header : Vect (S n) (Field label)) -> (nubProof : IsNub header) ->
                 (loc : Row k v header) ->
                 Header' n label
dropHeaderRow header nubProof loc =
  (dropRow header loc ** isNubFromOrdSub (ordSubFromDrop header loc) nubProof)

public export
dropHeaderField : (k : label) ->
                  (header : Vect (S n) (Field label)) ->
                  (nubProof : IsNub header) ->
                  {auto p : Row k v header} ->
                  Header' n label
dropHeaderField name header nubProof {p} = dropHeaderRow header nubProof p

public export
updateHeaderRow : (header : Vect n (Field label)) ->
                   (nubProof : IsNub header) ->
                   (loc : Row k v header) ->
                   (new : Type) ->
                   Header' n label
updateHeaderRow header nubProof loc new =
  (updateRow header loc new ** updatePreservesNub nubProof)


public export
updateHeaderField : (k : label) ->
                    (header : Vect n (Field label)) ->
                    (nubProof : IsNub header) ->
                    (new : Type) ->
                    {auto p : Row k v header} ->
                    Header' n label
updateHeaderField name header nubProof new {p} =
  updateHeaderRow header nubProof p new


public export
data Record' : (Header' n label) -> Type where
  Nil : Record' ([] ** [])
  (::) : DecEq label =>
         {l : label} ->
         {auto newPrf : NotKey l xs} ->
         t -> Record' (xs ** prf) ->
         Record' (((l, t) :: xs) ** (newPrf::prf))

%name Record' rec, xs, ys, zs

public export
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

t_record_4 : Record ["Foobar" := Maybe String, "Foo" := String, "Bar" := Nat]
t_record_4 = Just "Test2" :: t_record_3

t_record_4' : Record ["Foobar" := Maybe String, "Foo" := String, "Bar" := Nat]
t_record_4' = [Nothing, "Test", 19]

export
atRow : (rec : Record' (xs ** prf)) -> (loc : Row label ty xs) -> ty
atRow (x :: _) Here = x
atRow (_ :: rec) (There later) = atRow rec later

export
get : (field : a) -> (rec : Record' (xs ** prf)) -> {auto p : Row field ty xs} -> ty
get field rec {p} = atRow rec p

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
dropRow : {header : Vect (S n) (Field a)} ->
           (rec : Record' (header ** nubProof)) -> (p : Row k v header) ->
           Record' (dropHeaderRow header nubProof p)
dropRow rec p {header} = ordSubRecord rec (ordSubFromDrop header p)

export
dropField : {header : Vect (S n) (Field a)} ->
            (k : a) -> (rec : Record' (header ** nubProof)) ->
            {auto p : Row k v header} ->
            Record' (dropHeaderField k header nubProof)
dropField name rec {p} {header} = ordSubRecord rec (ordSubFromDrop header p)

t_drop_1 : Record ["Bar" := Nat]
t_drop_1 = dropRow t_record_3 Here

t_drop_2 : Record ["Bar" := Nat]
t_drop_2 = dropField "Foo" t_record_3

t_drop_3 : Record ["Foo" := String]
t_drop_3 = dropRow t_record_3 (There Here)

t_drop_4 : Record ["Foo" := String]
t_drop_4 = dropField "Bar" t_record_3

export
updateRow : {header : Vect n (Field a)} ->
             (rec : Record' (header ** nubProof)) ->
             (loc : Row k ty header) -> (ty -> tNew) ->
             Record' (updateHeaderRow header nubProof loc tNew)
updateRow (x :: xs) Here f = f x :: xs
updateRow (x :: xs) (There later) f = x :: updateRow xs later f

export
updateField : {header : Vect n (Field a)} ->
             (k : a) ->
             (ty -> tNew) ->
             (rec : Record' (header ** nubProof)) ->
             {auto p : Row k ty header} ->
             Record' (updateHeaderField k header nubProof tNew)
updateField k f xs {p} = updateRow xs p f

t_update_1 : Record ["Foo" := Nat, "Bar" := Nat]
t_update_1 = updateRow t_record_3 Here length

t_update_2 : Record ["Foo" := String, "Bar" := String]
t_update_2 = updateField "Bar" (const "BAAAAAR") t_record_3

export
subRecord : Record' (header ** nubProof) ->
            (subPrf : Sub sub header) ->
            Record' (sub ** isNubFromSub subPrf nubProof)
subRecord [] Empty = []
subRecord (x :: rec) (Skip sub) = subRecord rec sub
subRecord rec (Keep e sub) {nubProof = p :: pf} = atRow rec e :: subRecord (dropRow rec e) sub

export
sub : Record' (pre ** nubProof) -> {auto prf : Sub post pre} ->
      Record' (post ** isNubFromSub prf nubProof)
sub rec {prf} = subRecord rec prf

t_sub_1 : Record ["Bar" := Nat, "Foo" := String]
t_sub_1 = sub t_record_4

t_sub_2 : Record ["Bar" := Nat, "Foo" := String]
t_sub_2 = sub t_record_3

export
permuteRecord : Record' (header ** nubProof) ->
            (permPrf : Permute sub header) ->
            Record' (sub ** isNubFromPermute permPrf nubProof)
permuteRecord [] Empty = []
permuteRecord rec (Keep e sub) {nubProof = p :: pf} = atRow rec e :: permuteRecord (dropRow rec e) sub

export
rearrange : Record' (pre ** nubProof) -> {auto prf : Permute post pre} ->
            Record' (post ** isNubFromPermute prf nubProof)
rearrange rec {prf} = permuteRecord rec prf

t_rearrange_1 : Record ["Bar" := Nat, "Foo" := String]
t_rearrange_1 = rearrange t_record_3


export
merge : DecEq label =>
        {left : Vect n (Field label)} ->
        Record' (left ** leftNub) -> Record' (right ** rightNub) ->
        {auto prf : Disjoint left right} ->
        Record' (left ++ right ** disjointNub left leftNub right rightNub prf)
merge [] rightRec = rightRec
merge (x :: leftRec) rightRec {prf = pf :: prf} = x :: merge leftRec rightRec

t_merge : Record ["Foo" := Nat] -> Record ["Bar" := String] ->
          Record ["Foo" := Nat, "Bar" := String]
t_merge x y = merge x y

public export
mergeOnHeader : DecEq label =>
                (k : label) ->
                (ty : Type) ->
                (left  : Vect n (label, Type)) -> (nubLeft : IsNub left) ->
                (right : Vect (S m) (label, Type)) -> (nubRight : IsNub right) ->
                (rightLoc : Row k ty right) ->
                (prf : Disjoint left (dropRow right rightLoc)) ->
                Header' (n + m) label
mergeOnHeader k ty left nubLeft right nubRight rightLoc {prf} =
  (  left ++ dropRow right rightLoc
  ** disjointNub left nubLeft
       (dropRow right rightLoc)
       (isNubFromOrdSub (ordSubFromDrop right rightLoc) nubRight)
       prf
  )

export
mergeOn : (DecEq label, Eq ty) =>
          (k : label) ->
          Record' (left  ** leftNub)  ->
          Record' (right ** rightNub) ->
          {auto leftLoc  : Row k ty left}  ->
          {auto rightLoc : Row k ty right} ->
          {auto prf : Disjoint left (dropRow right rightLoc)} ->
          Maybe (Record' (mergeOnHeader k ty left leftNub right rightNub rightLoc prf))
mergeOn k left right = let
  l = get k left
  r = get k right
  in guard (l == r) *> pure (merge left (dropField k right))



export
decKey : DecEq a =>
           {header : Vect n (Field a)} ->
           (k : a) -> (rec : Record' (header ** nubProof)) -> Dec (ty ** Row k ty header)
decKey k rec {header} = decKey k header


