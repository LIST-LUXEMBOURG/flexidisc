module CleanRecord.RecordContent

import CleanRecord.OrdHeader
import CleanRecord.TaggedValue
import CleanRecord.THList

%default total
%access export

data RecordContent : (k : Type) -> (o : Ord k) -> (OrdHeader k o) -> Type where
  Empty : RecordContent k o []
  Cons  : TaggedValue k' a -> RecordContent k o xs ->
          RecordContent k o ((k', a) :: xs)

%name RecordContent xs, ys, zs

(::) : TaggedValue k' a -> RecordContent k o header ->
         RecordContent k o (insert (k',a) header)
(::) x Empty = Cons x Empty
(::) (k' := v) (Cons (kx := vx) xs') with (k' < kx)
  | False = Cons (kx := vx) ((k' := v) :: xs')
  | True  = Cons (k' := v) (Cons (kx := vx) xs')

Nil : (o : Ord k) => RecordContent k o []
Nil = Empty

atLabel : RecordContent k o header -> (loc : OrdLabel l header) -> atLabel header loc
atLabel (Cons (l := x) _) Here      = x
atLabel (Cons _ xs) (There later) = atLabel xs later


set : RecordContent k o header -> (loc : OrdLabel l header) -> (new : ty) ->
      RecordContent k o (changeType header loc ty)
set (Cons (l := x) xs) Here new = Cons (l := new) xs
set (Cons x xs) (There later) new = Cons x (set xs later new)

update : RecordContent k o header -> (loc : OrdRow l a header) ->
         (f : a -> b) ->
         RecordContent k o (changeType header loc b)
update (Cons (l := x) xs) Here f = Cons (l := f x) xs
update (Cons x xs) (There later) f = Cons x (update xs later f)


drop : RecordContent k o header -> (loc : OrdLabel l header) ->
       RecordContent k o (dropLabel header loc)
drop (Cons (l := x) xs) Here = xs
drop (Cons x xs) (There later) = Cons x (drop xs later)


project : RecordContent k o header -> Sub sub header ->
          RecordContent k o sub
project Empty Empty = Empty
project (Cons x ys) (Skip sub) = project ys sub
project (Cons x ys) (Keep sub) = Cons x (project ys sub)

keep : (xs : RecordContent k o pre) -> (sub : SubWithKeys keys post pre) ->
       RecordContent k o post
keep xs = project xs . toSub

discard : (xs : RecordContent k o pre) -> (sub : CompWithKeys keys post pre) ->
          RecordContent k o post
discard xs = project xs . toSub

toTHList : RecordContent k o header -> THList (toList header)
toTHList Empty = []
toTHList (Cons (_ := x) xs) = x :: toTHList xs

implementation Eq (RecordContent k o []) where
  (==) x y = True
  (/=) x y = False

implementation
(Eq t, Eq (RecordContent k o ts)) => Eq (RecordContent k o ((l,t)::ts)) where
  (==) (Cons (_ := x) xs) (Cons (_ := y) ys) = x == y && xs == ys
  (/=) (Cons (_ := x) xs) (Cons (_ := y) ys) = x /= y || xs /= ys
