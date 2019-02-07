module Test

import CleanRecord.Dec.IsYes
import CleanRecord.OrdHeader
import CleanRecord.TaggedValue
import CleanRecord.THList

import public CleanRecord.Header

%default total

namespace RC

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

namespace Record

  data Record : (k : Type) -> Header k -> Type where
    Rec : (o : Ord k) => RecordContent k o header -> Nub header -> Record k (H header)

  ||| Build a `Record` from a list of values, the function checks unicity of
  ||| the fields and build the `Record` if such proof can be generated
  rec : (xs : RecordContent k o header) -> {auto nubProof : Nub header} ->
        Record k (H header)
  rec xs {nubProof} = Rec xs nubProof

  Nil : Ord k => Record k []
  Nil = Rec [] []

  freshInsert : (DecEq k, Ord k) =>
                {k' : k} ->
                IsFresh k' header -> Nub header ->
                Nub (insert (k', ty) header)
  freshInsert fresh isnub {k'} {ty} {header} =
    isNubFromPermute (insertConsPermute (k', ty) header) (fresh :: isnub)

  (::) : (DecEq k, Ord k) => TaggedValue k' ty -> Record k (H header) ->
           {default SoTrue fresh : IsFresh k' header} ->
           Record k ((k',ty) :: H header)
  (::) x (Rec xs isnub) {fresh} = Rec (x :: xs) (freshInsert fresh isnub)

  atLabel : Record k header -> (loc : Label l header) -> atLabel header loc
  atLabel (Rec xs _) (L loc) = atLabel xs loc

  get : Record k header -> (query : k) ->
        {auto loc : Label query header} -> atLabel header loc
  get xs _ {loc} = atLabel xs loc

  toTHList : Record k header -> THList (toList header)
  toTHList (Rec xs _) = toTHList xs

  implementation
  Eq (THList (toList header)) => Eq (Record k header) where
    (==) xs ys = toTHList xs == toTHList ys
    (/=) xs ys = toTHList xs /= toTHList ys
