module CleanRecord.RecordContent

import public CleanRecord.Disjoint
import public CleanRecord.IsNo
import public CleanRecord.Label
import public CleanRecord.NegSub
import public CleanRecord.Nub
import public CleanRecord.OrdSub
import public CleanRecord.Permutation
import public CleanRecord.Row
import public CleanRecord.Sub

import public Data.Vect

%default total

public export
Field : (label : Type) -> Type
Field label = Pair label Type

public export
data RecordContent : Vect n (Field label) -> Type where
  Nil : RecordContent []
  (::) : ty -> RecordContent header -> RecordContent ((lbl, ty) :: header)

public export
types : Vect n (Field label) -> Vect n Type
types = map snd

public export
interface Eqs (ts : Vect n (Field a)) where
  eqs : RecordContent ts -> RecordContent ts ->
        Bool

public export
implementation Eqs [] where
  eqs [] [] = True

public export
implementation (Eq t, Eqs ts) => Eqs ((a, t)::ts) where
  eqs (x :: xs) (y :: ys) = x == y && eqs xs ys

public export
implementation Eqs ts => Eq (RecordContent ts) where
  (==) xs ys = eqs xs ys


export
(++) : RecordContent left -> RecordContent right -> RecordContent (left ++ right)
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

export
atRow : (rec : RecordContent xs) -> (loc : Row label ty xs) -> ty
atRow (x :: _)  Here = x
atRow (_ :: xs) (There later) = atRow xs later

export
ordSub : RecordContent header ->
         (ordsubPrf : OrdSub sub header) ->
         RecordContent sub
ordSub [] Empty = []
ordSub (x :: xs) (Skip sub) = ordSub xs sub
ordSub (x :: xs) (Keep sub) = x :: ordSub xs sub

export
updateRow : {header : Vect n (Field a)} ->
            (xs : RecordContent header) ->
            (loc : Row k ty header) -> (ty -> tNew) ->
            RecordContent (updateRow header loc tNew)
updateRow (x :: xs) Here f = f x :: xs
updateRow (x :: xs) (There later) f = x :: updateRow xs later f

export
replaceRow : {header : Vect n (Field a)} ->
            (xs : RecordContent header) ->
            (loc : Label k header) -> tNew ->
            RecordContent (updateLabel header loc tNew)
replaceRow (x :: xs) Here new = new :: xs
replaceRow (x :: xs) (There later) new = x :: replaceRow xs later new

export
dropRow : {header : Vect (S n) (Field a)} ->
          RecordContent header -> (loc : Label k header) ->
          RecordContent (dropLabel header loc)
dropRow (_ :: xs) Here = xs
dropRow {n = S n} (x :: xs) (There later) = x :: dropRow xs later

export
project : RecordContent header ->
                 (subPrf : Sub sub header) ->
                 RecordContent sub
project [] Empty = []
project (x :: xs) (Skip sub) = project xs sub
project xs (Keep e sub) =
  atRow xs e :: project (dropRow xs (labelFromRow e)) sub

export
negProject : RecordContent header ->
                 (negPrf : NegSub sub header) ->
                 RecordContent sub
negProject [] Empty = []
negProject xs (Skip e sub) = negProject (dropRow xs e) sub
negProject (x::xs) (Keep sub) = x :: negProject xs sub

export
reorder : RecordContent header ->
                 (permPrf : Permute sub header) ->
                 RecordContent sub
reorder [] Empty = []
reorder xs (Keep e sub) =
  atRow xs e :: reorder (dropRow xs (labelFromRow e)) sub

infix 8 ::=

namespace NamedContent

  public export
  data Row : (k : key) -> Type -> Type where
    MkRow : v -> Row k v

  export
  (::=) : (k : key) -> value -> Row k value
  (::=) k v = MkRow v

  public export
  data NamedRecordContent : Vect n (Field label) -> Type where
    Nil : NamedRecordContent []
    (::) : Row lbl ty -> NamedRecordContent header -> NamedRecordContent ((lbl, ty) :: header)

  export
  toRecordContent : NamedRecordContent xs -> RecordContent xs
  toRecordContent [] = []
  toRecordContent ((MkRow x) :: xs) = x :: toRecordContent xs
