module CleanRecord.RecordContent

import CleanRecord.OrdHeader
import CleanRecord.TaggedValue
import CleanRecord.THList

%default total
%access export

public export
data RecordContent : (k : Type) -> (o : Ord k) -> (OrdHeader k o) -> Type where
  Nil  : RecordContent k o []
  (::) : TaggedValue k' a -> RecordContent k o xs ->
         RecordContent k o ((k', a) :: xs)

%name RecordContent xs, ys, zs

export
empty : RecordContent k o []
empty = Nil

insert : TaggedValue k' a -> RecordContent k o header ->
         RecordContent k o (insert (k',a) header)
insert x [] = [x]
insert (k' := v) ((kx := vx) :: xs') with (k' < kx)
  | False = (kx := vx) :: (insert (k' := v) xs')
  | True  = (k' := v) :: (kx := vx) :: xs'

atLabel : RecordContent k o header -> (loc : OrdLabel l header) -> atLabel header loc
atLabel ((l := x) :: _) Here      = x
atLabel (_ :: xs) (There later) = atLabel xs later


atRow : RecordContent k o header -> (loc : OrdRow l ty header) -> ty
atRow ((l := x) :: _) Here      = x
atRow (_ :: xs) (There later) = atRow xs later


set : RecordContent k o header -> (loc : OrdLabel l header) -> (new : ty) ->
      RecordContent k o (changeType header loc ty)
set ((l := x) :: xs) Here          new = (l := new) :: xs
set (x :: xs)        (There later) new = x          :: set xs later new

setByRow : RecordContent k o header -> (loc : OrdRow l tOld header) ->
           (new : tNew) ->
           RecordContent k o (changeValue header loc tNew)
setByRow ((l := x) :: xs) Here          new = (l := new) :: xs
setByRow (x :: xs)        (There later) new = x :: setByRow xs later new

update : RecordContent k o header -> (loc : OrdRow l a header) ->
         (f : a -> b) ->
         RecordContent k o (changeValue header loc b)
update ((l := x) :: xs) Here f = (l := f x) :: xs
update (x :: xs) (There later) f = x :: update xs later f

merge : (xs : RecordContent k o header) -> (ys : RecordContent k o header') ->
        RecordContent k o (merge header header')
merge [] ys = ys
merge (x :: zs) [] = x :: zs
merge ((k := x) :: zs) ((k' := y) :: ys) with (k < k')
  | True  = (k  := x) :: (merge zs ((k' := y) :: ys))
  | False = (k' := y) :: (merge ((k := x) :: zs) ys)

diff : DecEq k =>
       (xs : RecordContent k o header) -> (ys : RecordContent k o header') ->
       RecordContent k o (diffKeys header header')
diff [] ys = []
diff (kx := vx :: xs) ys {header'} with (decFresh kx header')
  | (Yes prf) = kx := vx :: diff xs ys
  | (No contra) = diff xs ys

infixl 7 |>

(|>) : DecEq k =>
             (xs : RecordContent k o header) -> (ys : RecordContent k o header') ->
        RecordContent k o (patch header header')
(|>) xs ys = merge (diff ys xs) xs


drop : RecordContent k o header -> (loc : OrdLabel l header) ->
       RecordContent k o (dropLabel header loc)
drop ((l := x) :: xs) Here = xs
drop (x :: xs) (There later) = x :: drop xs later


project : RecordContent k o header -> Sub sub header ->
          RecordContent k o sub
project [] Empty = []
project (x :: ys) (Skip sub) = project ys sub
project (x :: ys) (Keep sub) = x :: project ys sub

keep : (xs : RecordContent k o pre) -> (sub : SubWithKeys keys post pre) ->
       RecordContent k o post
keep xs = project xs . toSub

discard : (xs : RecordContent k o pre) -> (sub : CompWithKeys keys post pre) ->
          RecordContent k o post
discard xs = project xs . toSub

optional : (xs : RecordContent k o pre) -> (opt : HereOrNot post pre) ->
           RecordContent k o (optional post)
optional [] Empty = []
optional xs (Skip compat yes) = _ := Nothing :: optional xs compat
optional (x :: xs) (Extra compat yes) = optional xs compat
optional (l := v :: xs) (Keep compat) = l := Just v :: optional xs compat

toTHList : RecordContent k o header -> THList k (toList header)
toTHList [] = []
toTHList ((_ := x) :: xs) = x :: toTHList xs

implementation Eq (RecordContent k o []) where
  (==) x y = True
  (/=) x y = False

implementation
(Eq t, Eq (RecordContent k o ts)) => Eq (RecordContent k o ((l,t) :: ts)) where
  (==) ((_ := x) :: xs) ((_ := y) :: ys) = x == y && xs == ys
  (/=) ((_ := x) :: xs) ((_ := y) :: ys) = x /= y || xs /= ys
