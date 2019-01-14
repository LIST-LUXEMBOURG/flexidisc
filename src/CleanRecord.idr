module CleanRecord

import Data.Vect

%default total

namespace Field

  public export
  Field : (label : Type) -> Type
  Field label = Pair label Type

  public export
  data Elem : (lbl : label) -> (t : ty) -> Vect n (label, ty) -> Type where
    Here : Elem lbl t ((lbl, t) :: xs)
    There : (later : Elem lbl t xs) -> Elem lbl t (x::xs)

  public export
  Uninhabited (Elem x ty []) where
    uninhabited Here impossible
    uninhabited (There _) impossible

  public export
  dropElem : (xs : Vect (S n) (a, b)) -> (p : Elem x ty xs) -> Vect n (a, b)
  dropElem (_ :: ys) Here = ys
  dropElem {n = S n} (x :: ys) (There later) = x :: dropElem ys later

  public export
  updateElem : (xs : Vect n (a, b)) -> (p : Elem x old xs) -> (new : b) -> Vect n (a, b)
  updateElem ((x, ty) :: xs) Here new = (x, new) :: xs
  updateElem (x :: xs) (There later) new = x :: updateElem xs later new

  public export
  elemFromDrop : {xs : Vect (S n) (a,b)} -> {e : Elem k v xs} ->
                 Elem x ty (dropElem xs e) -> Elem x ty xs
  elemFromDrop loc {e = Here} = There loc
  elemFromDrop Here {e = (There later)} = Here
  elemFromDrop (There loc) {e = (There later)} = There (elemFromDrop loc)


  public export
  labels : Vect n (a, b) -> Vect n a
  labels [] = []
  labels (x::xs) = fst x :: labels xs

  public export
  hasField : DecEq label => (lbl : label) -> (xs : Vect n (label, b)) -> Dec (ty ** Elem lbl ty xs)
  hasField lbl [] = No (\pf => absurd (snd pf))
  hasField lbl ((k, v) :: xs) with (decEq lbl k)
    | (Yes prf) = rewrite prf in Yes (v ** Here)
    | (No notHere) with (hasField lbl xs)
      | (Yes (t ** loc)) = Yes (t ** There loc)
      | (No notThere) = No (\(ty ** loc) => case loc of
                           Here => absurd (notHere Refl)
                           There later => absurd (notThere (ty ** later)))

  ||| Build at type level the proof that a decidable property is valid
  public export
  data IsNo : prop -> Type where
    SoFalse : IsNo (No prop)

  ||| Demote an absurd proof from the type level to the value level
  public export
  getContra : {witness : Dec prop} -> IsNo witness -> (Not prop)
  getContra x {witness = (Yes prf)} impossible
  getContra x {witness = (No contra)} = contra

  public export
  notElemFromEvidence : DecEq a => {x : a} -> (prf : Not (ty ** Elem x ty xs)) -> IsNo (hasField x xs)
  notElemFromEvidence prf {x} {xs} with (hasField x xs)
    | (Yes y) = absurd (prf y)
    | (No contra) = SoFalse


namespace Nub

  ||| Proof that all elements in a vector are distincts
  public export
  data IsNub : Vect n (a, b) -> Type where
    Nil : IsNub []
    (::) : DecEq a => {x : a} -> IsNo (hasField x xs) -> IsNub xs -> IsNub ((x, ty)::xs)

  public export
  decNub : DecEq a => (xs : Vect n (a, b)) -> Dec (IsNub xs)
  decNub [] = Yes []
  decNub ((k,v) :: xs) with (decNub xs)
    | (Yes prf) with (hasField k xs)
      | (Yes y)     = No (\(p :: _) => getContra p y)
      | (No contra) = Yes (notElemFromEvidence contra :: prf)
    | (No contra) = No (\(_ :: prf) => contra prf)

  public export
  mapElemOnUpdate : DecEq a => {k : a} -> (v ** Elem k v (updateElem xs p new)) -> (v' ** Elem k v' xs)
  mapElemOnUpdate _ {p = Here} {xs = []} impossible
  mapElemOnUpdate _ {p = (There _)} {xs = []} impossible
  mapElemOnUpdate (v ** Here) {p = Here} {xs = (k, old) :: xs} = (old ** Here)
  mapElemOnUpdate (v ** There later) {p = Here} {xs = (k, old) :: xs} = (v ** There later)
  mapElemOnUpdate (y ** Here) {p = (There later)} {xs = (x, y) :: xs} = (y ** Here)
  mapElemOnUpdate (y ** There e) {p = (There later)} {xs = x :: xs} with (mapElemOnUpdate (y ** e))
    | (z ** pf) = (z ** There pf)

  public export
  updatePreservesNotField : DecEq a =>
                            {x : a} -> (p : IsNo (hasField x xs)) -> IsNo (hasField x (updateElem xs e new))
  updatePreservesNotField p = notElemFromEvidence (getContra p . mapElemOnUpdate)

  public export
  updatePreservesNub : IsNub xs -> IsNub (updateElem xs e new)
  updatePreservesNub [] {e} = absurd e
  updatePreservesNub (p :: pf) {e = Here} = p :: pf
  updatePreservesNub (p :: pf) {e = (There later)} = updatePreservesNotField p :: updatePreservesNub pf

namespace OrdSub

  public export
  data OrdSub : (xs : Vect n a) -> (ys : Vect m a) -> Type where
    Empty : OrdSub [] []
    Skip  : OrdSub xs ys -> OrdSub xs (y::ys)
    Keep  : OrdSub xs ys -> OrdSub (x::xs) (x::ys)

  public export
  ordSubEmpty' : (xs : Vect n a) -> OrdSub [] xs
  ordSubEmpty' [] = Empty
  ordSubEmpty' (_ :: xs) = Skip (ordSubEmpty' xs)

  public export
  ordSubEmpty : OrdSub [] xs
  ordSubEmpty {xs} = ordSubEmpty' xs

  public export
  ordSubRefl' : (xs : Vect n a) -> OrdSub xs xs
  ordSubRefl' [] = Empty
  ordSubRefl' (x :: xs) = Keep (ordSubRefl' xs)

  public export
  ordSubRefl : OrdSub xs xs
  ordSubRefl {xs} = ordSubRefl' xs

  public export
  elemFromOrdSub : OrdSub xs ys -> Elem x ty xs -> Elem x ty ys
  elemFromOrdSub (Keep _)   Here          = Here
  elemFromOrdSub (Keep ord) (There later) = There (elemFromOrdSub ord later)
  elemFromOrdSub (Skip ord) loc           = There (elemFromOrdSub ord loc)

  public export
  notInOrdSub : DecEq a => {x : a} -> OrdSub ys xs -> Not (t ** Elem x t xs) -> IsNo (hasField x ys)
  notInOrdSub sub contra {x} {ys} with (hasField x ys)
    | (Yes (t ** loc)) = absurd (contra (t ** elemFromOrdSub sub loc))
    | (No f) = SoFalse

  public export
  ordSubFromDrop : (xs : Vect (S k) (a, b)) -> (loc : Elem x ty xs) -> OrdSub (dropElem xs loc) xs
  ordSubFromDrop ((x, ty) :: ys) Here = Skip ordSubRefl
  ordSubFromDrop {k = S k} (x :: ys) (There later) = Keep (ordSubFromDrop ys later)

  public export
  isNubFromOrdSub : OrdSub xs ys -> IsNub ys -> IsNub xs
  isNubFromOrdSub Empty [] = []
  isNubFromOrdSub (Skip x) (p :: pf) = isNubFromOrdSub x pf
  isNubFromOrdSub (Keep x) (p :: pf) = notInOrdSub x (getContra p) :: isNubFromOrdSub x pf


namespace Sub

  public export
  data Sub : (sub : Vect n (a, b)) -> (initial : Vect m (a, b)) -> Type where
    Empty : Sub [] []
    Skip  : Sub sub initial -> Sub sub ((k,v)::initial)
    Keep  : (e : Elem k v initial) -> Sub keep (dropElem initial e) -> Sub ((k,v)::keep) initial

  public export
  subEmpty' : (xs : Vect n (a, b)) -> Sub [] xs
  subEmpty' [] = Empty
  subEmpty' ((k, v) :: xs) = Skip (subEmpty' xs)

  public export
  subEmpty : Sub [] xs
  subEmpty {xs} = subEmpty' xs

  public export
  subRefl' : (xs : Vect n (a, b)) -> Sub xs xs
  subRefl' [] = Empty
  subRefl' ((k, v) :: xs) = Keep Here (subRefl' xs)

  public export
  subRefl : Sub xs xs
  subRefl {xs} = subRefl' xs


  public export
  elemFromSub : Sub xs ys -> Elem x ty xs -> Elem x ty ys
  elemFromSub Empty y = y
  elemFromSub (Skip z) loc = There (elemFromSub z loc)
  elemFromSub (Keep e _) Here = e
  elemFromSub (Keep e sub) (There later) = elemFromDrop (elemFromSub sub later)

  public export
  notInSub : DecEq a => {k: a} -> Sub ys xs -> Not (v ** Elem k v xs) -> IsNo (hasField k ys)
  notInSub sub contra {k} {ys} with (hasField k ys)
    | (Yes (t ** loc)) = absurd (contra (t ** elemFromSub sub loc))
    | (No _) = SoFalse


  public export
  removeFromNubIsNotThere : DecEq a =>
                            {k : a} ->
                            IsNub xs -> (ePre : Elem k v xs) -> Not (v' ** Elem k v' (dropElem xs ePre))
  removeFromNubIsNotThere (p :: _) Here next = absurd (getContra p next)
  removeFromNubIsNotThere (p :: prf) (There later) (_ ** Here) {v} = absurd (getContra p (v ** later))
  removeFromNubIsNotThere (p :: prf) (There later) (x ** There loc) = removeFromNubIsNotThere prf later (x ** loc)

  public export
  moveFirst : DecEq a => {k : a} -> IsNub xs -> (e : Elem k v xs) -> IsNub ((k, v) :: dropElem xs e)
  moveFirst prf e = notElemFromEvidence (removeFromNubIsNotThere prf e) :: isNubFromOrdSub (ordSubFromDrop _ e) prf

  public export
  isNubFromSub : Sub xs ys -> IsNub ys -> IsNub xs
  isNubFromSub Empty [] = []
  isNubFromSub (Skip z) (p :: pf) = isNubFromSub z pf
  isNubFromSub (Keep e z) (p :: pf) = notInSub z (removeFromNubIsNotThere (p::pf) e) :: isNubFromSub z (isNubFromOrdSub (ordSubFromDrop _ e) (p::pf))



namespace Header

  public export
  Header' : (n : Nat) -> (label : Type) -> Type
  Header' n label = DPair (Vect n (Field label)) IsNub

  public export
  Header : DecEq a => (xs : Vect n (Field a)) -> {auto prf : IsNub xs} -> Header' n a
  Header xs {prf} = (xs ** prf)

namespace Record

  export
  data Record' : (Header' n label) -> Type where
    Nil : Record' ([] ** [])
    (::) : DecEq label =>
           {l : label} -> {auto newPrf : IsNo (hasField l xs)} ->
           t -> Record' (xs ** prf) ->
           Record' (((l, t) :: xs) ** (newPrf::prf))

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

  t_record3 : Record ["Foo" := String, "Bar" := Nat]
  t_record3 = ["Test", 42]

  t_record3' : Record ["Foo" := String, "Bar" := Nat]
  t_record3' = "Test" :: t_record1

  export
  atElem : (loc : Elem label ty xs) -> (rec : Record' (xs ** prf)) -> ty
  atElem Here (x :: _) = x
  atElem (There later) (_ :: rec) = atElem later rec

  export
  get : (field : a) -> (rec : Record' (xs ** prf)) -> {auto p : Elem field ty xs} -> ty
  get field rec {p} = atElem p rec

  t_get_1 : String
  t_get_1 = get "Foo" t_record3

  t_get_2 : Nat
  t_get_2 = get "Bar" t_record3

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
             Record' (dropElem header p ** isNubFromOrdSub (ordSubFromDrop header p) nubProof)
  dropElem rec p {header} = ordSubRecord rec (ordSubFromDrop header p)

  export
  dropField : {header : Vect (S n) (Field a)} ->
              (k : a) -> (rec : Record' (header ** nubProof)) -> {auto p : Elem k v header} ->
              Record' (dropElem header p ** isNubFromOrdSub (ordSubFromDrop header p) nubProof)
  dropField name rec {p} {header} = ordSubRecord rec (ordSubFromDrop header p)

  t_drop_1 : Record ["Bar" := Nat]
  t_drop_1 = dropElem t_record3 Here

  t_drop_2 : Record ["Bar" := Nat]
  t_drop_2 = dropField "Foo" t_record3

  t_drop_3 : Record ["Foo" := String]
  t_drop_3 = dropElem t_record3 (There Here)

  t_drop_4 : Record ["Foo" := String]
  t_drop_4 = dropField "Bar" t_record3

  export
  updateElem : {header : Vect n (Field a)} ->
               (rec : Record' (header ** nubProof)) -> (p : Elem k ty header) ->
               (ty -> tNew) ->
               Record' (updateElem header p tNew ** updatePreservesNub nubProof)
  updateElem (x :: xs) Here f = f x :: xs
  updateElem (x :: xs) (There later) f = x :: updateElem xs later f

  export
  updateField : {header : Vect n (Field a)} ->
               (k : a) ->
               (ty -> tNew) ->
               (rec : Record' (header ** nubProof)) ->
               {auto p : Elem k ty header} ->
               Record' (updateElem header p tNew ** updatePreservesNub nubProof)
  updateField k f xs {p} = updateElem xs p f

  t_update_1 : Record ["Foo" := Nat, "Bar" := Nat]
  t_update_1 = updateElem t_record3 Here length

  t_update_2 : Record ["Foo" := String, "Bar" := String]
  t_update_2 = updateField "Bar" (const "BAAAAAR") t_record3

  export
  subRecord : Record' (header ** nubProof) ->
              (subPrf : Sub sub header) ->
              Record' (sub ** isNubFromSub subPrf nubProof)
  subRecord [] Empty = []
  subRecord (x :: rec) (Skip sub) = subRecord rec sub
  subRecord rec (Keep e sub) {nubProof = p :: pf} = atElem e rec :: subRecord (dropElem rec e) sub

  export
  rearrange : Record' (pre ** nubProof) -> {auto prf : Sub post pre} ->
              Record' (post ** isNubFromSub prf nubProof)
  rearrange rec {prf} = subRecord rec prf

  t_rearrange : Record ["Bar" := Nat, "Foo" := String]
  t_rearrange = rearrange t_record3

  export
  hasField : DecEq a =>
             {header : Vect n (Field a)} ->
             (k : a) -> (rec : Record' (header ** nubProof)) -> Dec (ty ** Elem k ty header)
  hasField k rec {header} = hasField k header
