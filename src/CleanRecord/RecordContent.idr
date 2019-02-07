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
