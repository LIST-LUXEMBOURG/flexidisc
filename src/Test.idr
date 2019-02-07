module Test

import CleanRecord.Dec.IsYes
import CleanRecord.OrdHeader
import CleanRecord.TaggedValue
import CleanRecord.THList

import public CleanRecord.Header

%default total

namespace Nub

  data Nub : (OrdHeader label o) -> Type where
    Nil  : Nub []
    (::) : DecEq k => {l : k} -> IsFresh l xs -> Nub xs -> Nub ((l,ty) :: xs)

  ||| Decide whether a list is made of different labelents or not
  decNub : DecEq label => (xs : OrdHeader label o) -> Dec (Nub xs)
  decNub [] = Yes []
  decNub ((l, ty) :: xs) with (decFresh l xs)
    | (Yes headFresh) with (decNub xs)
      | (Yes tailFresh) = Yes (isFreshFromEvidence headFresh :: tailFresh)
      | (No contra) = No (\ (_ :: tailFresh) => contra tailFresh)
    | (No contra) = No (\ (headFresh :: _) => contra (getProof headFresh))

  IsNub : DecEq label => (xs : OrdHeader label o) -> Type
  IsNub xs = IsYes (decNub xs)

  removeFromNubIsFresh : {k : key} ->
                         Nub xs -> (ePre : OrdLabel k xs) -> Fresh k (dropLabel xs ePre)
  removeFromNubIsFresh (yes :: isnub) Here = getProof yes
  removeFromNubIsFresh (yes :: isnub) (There later) =
    (\p => freshCantBeLabel (getProof yes) (rewrite (sym p) in later)) :: removeFromNubIsFresh isnub later

  dropPreservesFresh : Fresh l xs -> Fresh l (dropLabel xs e)
  dropPreservesFresh (f :: fresh) {e = Here} = fresh
  dropPreservesFresh (f :: fresh) {e = (There e)} = f :: dropPreservesFresh fresh

  dropPreservesNub : Nub xs -> (loc : OrdLabel l xs) -> Nub (dropLabel xs loc)
  dropPreservesNub (yes :: x) Here = x
  dropPreservesNub (yes :: x) (There later) =
    isFreshFromEvidence (dropPreservesFresh (getProof yes)) :: dropPreservesNub x later



namespace Permute

  ||| Proof that a `Vect` is a permutation of another vect
  data Permute : (xs : OrdHeader k o) ->
                 (ys : OrdHeader k o) ->
                 Type where
    Empty : Permute [] []
    Keep  : (e : OrdRow k ty ys) -> Permute xs (dropOrdRow ys e) ->
            Permute ((k, ty)::xs) ys

  permuteRefl : (xs : OrdHeader k o) -> Permute xs xs
  permuteRefl [] = Empty
  permuteRefl ((k, v)::xs) = Keep Here (permuteRefl xs)

  insertConsPermute : (x : (k, Type)) -> (xs : OrdHeader k o) -> Permute  (insert x xs) (x :: xs)
  insertConsPermute (k, ty) [] = Keep Here Empty
  insertConsPermute (k, ty) ((kx, tx) :: xs) with (k < kx)
    | True  = Keep Here (Keep Here (permuteRefl xs))
    | False = Keep (There Here) (insertConsPermute (k, ty) xs)

  consInsertPermute : (x : (k, Type)) -> (xs : OrdHeader k o) -> Permute  (x :: xs) (insert x xs)
  consInsertPermute (l, ty) xs =
    Keep (findInsertOrdRow l xs)
         (rewrite dropInsertInv l ty xs in (permuteRefl xs))

  permutePreservesFresh :  Permute ys xs -> Fresh k xs -> Fresh k ys
  permutePreservesFresh Empty fresh = fresh
  permutePreservesFresh (Keep e perm) fresh =
    (\p => freshCantBeLabel fresh (rewrite p in labelFromOrdRow e)) ::
    permutePreservesFresh perm (dropPreservesFresh fresh)

  isNubFromPermute : Permute xs ys -> Nub ys -> Nub xs
  isNubFromPermute Empty [] = []
  isNubFromPermute (Keep e perm) pf@(p::_) =
    isFreshFromEvidence
      (permutePreservesFresh perm (removeFromNubIsFresh pf (labelFromOrdRow e)))
    :: isNubFromPermute perm (dropPreservesNub pf (labelFromOrdRow e))

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
