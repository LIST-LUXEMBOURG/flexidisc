module Flexidisc.RecordContent

import Control.Monad.Identity
import Flexidisc.OrdHeader
import Flexidisc.TaggedValue
import Flexidisc.THList

%default total
%access export

public export
data RecordContentM : (m : Type -> Type) ->
                      (k : Type) -> (o : Ord k) -> (OrdHeader k o) -> Type where
  Nil  : RecordContentM m k o []
  (::) : TaggedValue k' (m a) -> RecordContentM m k o xs ->
         RecordContentM m k o ((k', a) :: xs)

cons : TaggedValue k' (m a) -> RecordContentM m k o xs ->
       RecordContentM m k o ((k', a) :: xs)
cons = (::)

%name RecordContentM xs, ys, zs

public export
RecordContent : (k : Type) -> (o : Ord k) -> (OrdHeader k o) -> Type
RecordContent = RecordContentM id

empty : RecordContentM m k o []
empty = Nil

insert : TaggedValue k' (m a) -> RecordContentM m k o header ->
         RecordContentM m k o (insert (k', a) header)
insert x [] = [x]
insert (k' := v) ((kx := vx) :: xs') with (k' < kx)
  | False = (kx := vx) :: (insert (k' := v) xs')
  | True  = (k' := v) :: (kx := vx) :: xs'

atLabel : RecordContentM m k o header -> (loc : OrdLabel l header) ->
          m (atLabel header loc)
atLabel ((l := x) :: _) Here      = x
atLabel (_ :: xs) (There later) = atLabel xs later

atRow : RecordContentM m k o header -> (loc : OrdRow l ty header) -> m ty
atRow ((l := x) :: _) Here      = x
atRow (_ :: xs) (There later) = atRow xs later

set : RecordContentM m k o header ->
      (loc : OrdLabel l header) -> (new : m ty) ->
      RecordContentM m k o (changeType header loc ty)
set ((l := x) :: xs) Here          new = (l := new) :: xs
set (x :: xs)        (There later) new = x          :: set xs later new

setByRow : RecordContentM m k o header ->
           (loc : OrdRow l tOld header) -> (new : m tNew) ->
           RecordContentM m k o (changeValue header loc tNew)
setByRow ((l := x) :: xs) Here          new = (l := new) :: xs
setByRow (x :: xs)        (There later) new = x :: setByRow xs later new

update : RecordContentM m k o header -> (loc : OrdRow l a header) ->
         (f : m a -> m b) ->
         RecordContentM m k o (changeValue header loc b)
update ((l := x) :: xs) Here f = (l := f x) :: xs
update (x :: xs) (There later) f = x :: update xs later f

merge : (xs : RecordContentM m k o header) ->
        (ys : RecordContentM m k o header') ->
        RecordContentM m k o (merge header header')
merge [] ys = ys
merge (x :: zs) [] = x :: zs
merge ((k := x) :: zs) ((k' := y) :: ys) with (k < k')
  | True  = (k  := x) :: (merge zs ((k' := y) :: ys))
  | False = (k' := y) :: (merge ((k := x) :: zs) ys)

diff : DecEq k =>
       (xs : RecordContentM m k o header) ->
       (ys : RecordContentM m k o header') ->
       RecordContentM m k o (diffKeys header header')
diff [] ys = []
diff (kx := vx :: xs) ys {header'} with (decFresh kx header')
  | (Yes prf) = kx := vx :: diff xs ys
  | (No contra) = diff xs ys

infixl 7 |>

(|>) : DecEq k =>
       (xs : RecordContentM m k o header) ->
       (ys : RecordContentM m k o header') ->
       RecordContentM m k o (patch header header')
(|>) xs ys = merge (diff ys xs) xs


drop : RecordContentM m k o header -> (loc : OrdLabel l header) ->
       RecordContentM m k o (dropLabel header loc)
drop ((l := x) :: xs) Here = xs
drop (x :: xs) (There later) = x :: drop xs later


project : RecordContentM m k o header -> Sub sub header ->
          RecordContentM m k o sub
project [] Empty = []
project (x :: ys) (Skip sub) = project ys sub
project (x :: ys) (Keep sub) = x :: project ys sub

keep : (xs : RecordContentM m k o pre) -> (sub : SubWithKeys keys post pre) ->
       RecordContentM m k o post
keep xs = project xs . toSub

discard : (xs : RecordContentM m k o pre) ->
          (sub : CompWithKeys keys post pre) ->
          RecordContentM m k o post
discard xs = project xs . toSub

hoist : (f: {a : _} -> m a -> n a) -> RecordContentM m k o header ->
        RecordContentM n k o header
hoist f [] = []
hoist f (l := v :: xs) = (l := f v) :: hoist f xs

lift : (f : {a : _} -> a -> m a) -> RecordContent k o header ->
        RecordContentM m k o header
lift = hoist

optional : (xs : RecordContent k o pre) -> (opt : HereOrNot post pre) ->
           RecordContentM Maybe k o post
optional [] Empty = []
optional xs (Skip compat yes) = _ := Nothing :: optional xs compat
optional (x :: xs) (Extra compat yes) = optional xs compat
optional (l := v :: xs) (Keep compat) = l := Just v :: optional xs compat

toTHList : RecordContentM m k o header -> THList m k (toList header)
toTHList [] = []
toTHList ((_ := x) :: xs) = x :: toTHList xs

sequence : Applicative m =>
           RecordContentM m k o header -> m (RecordContent k o header)
sequence [] = pure []
sequence ((k' := x) :: xs) = (map (cons . (k' :=)) x) <*> (sequence xs)

implementation Eq (RecordContentM m k o []) where
  (==) x y = True
  (/=) x y = False

implementation
(Eq (m t), Eq (RecordContentM m k o ts)) => Eq (RecordContentM m k o ((l,t) :: ts)) where
  (==) ((_ := x) :: xs) ((_ := y) :: ys) = x == y && xs == ys
  (/=) ((_ := x) :: xs) ((_ := y) :: ys) = x /= y || xs /= ys
