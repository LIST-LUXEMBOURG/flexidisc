module Test

%default total
%access public export

||| Build at type level the proof that a decidable property is valid
data IsYes : prop -> Type where
  SoTrue : IsYes (Yes prop)

getProof : {witness : Dec prop} -> IsYes witness -> prop
getProof yes {witness = (Yes prf)} = prf
getProof yes {witness = (No contra)} impossible

%name IsYes yes, prf, ok


infixl 8 :=

data TaggedValue : (key : k) -> (v : Type) -> Type where
  (:=) : (key : k) -> v -> TaggedValue key v


namespace HList

  data HList : (List (k, Type)) -> Type where
    Nil  : HList []
    (::) : a -> HList xs -> HList ((l, a)::xs)

  implementation Eq (HList []) where
    (==) x y = True
    (/=) x y = False

  implementation (Eq t, Eq (HList ts)) => Eq (HList ((k,t)::ts)) where
    (==) (x :: xs) (y :: ys) = x == y && xs == ys
    (/=) (x :: xs) (y :: ys) = x /= y || xs /= ys

namespace OrdHeader

  data OrdHeader : (k : Type) -> (Ord k) -> Type where
    Nil  : OrdHeader k o
    (::) : (k, Type) -> OrdHeader k o -> OrdHeader k o

  %name OrdHeader hs, xs, ys, zs

  insert : (k, Type) -> OrdHeader k o -> OrdHeader k o
  insert x []= [x]
  insert (k, v) ((k', v') :: xs) with (k < k')
    | False = (k',v') :: (insert (k, v) xs)
    | True  = (k,v)   :: (k',v') :: xs

  header : (o : Ord k) => List (k, Type) -> OrdHeader k o
  header = foldl (flip insert) Nil

  toList : OrdHeader k o -> List (k, Type)
  toList [] = []
  toList (x :: xs) = x :: toList xs

namespace Header

  data Header : (k : Type) -> Type where
    H : (o : Ord k) => OrdHeader k o -> Header k

  Nil : Ord k => Header k
  Nil = H []

  (::) : (k, Type) -> Header k -> Header k
  (::) x (H h) = H (insert x h)

  toList : Header k -> List (k, Type)
  toList (H xs) = toList xs

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

  toHList : RecordContent k o header -> HList (toList header)
  toHList Empty = []
  toHList (Cons (_ := x) xs) = x :: toHList xs

  implementation Eq (RecordContent k o []) where
    (==) x y = True
    (/=) x y = False

  implementation
  (Eq t, Eq (RecordContent k o ts)) => Eq (RecordContent k o ((l,t)::ts)) where
    (==) (Cons (_ := x) xs) (Cons (_ := y) ys) = x == y && xs == ys
    (/=) (Cons (_ := x) xs) (Cons (_ := y) ys) = x /= y || xs /= ys

namespace OrdLabel

  data OrdLabel : (k : l) -> (xs : OrdHeader l o) -> Type where
    Here : OrdLabel k ((k,v)::xs)
    There : (later : OrdLabel k xs) -> OrdLabel k (x::xs)

  %name OrdLabel lbl, loc, prf, e, elem

  atLabel : (xs : OrdHeader l o) -> (loc : OrdLabel k xs) -> Type
  atLabel ((_, v) :: _) Here = v
  atLabel (_ :: xs) (There later) = atLabel xs later

  Uninhabited (OrdLabel k []) where
    uninhabited Here      impossible
    uninhabited (There _) impossible

  ||| Given a proof that an element is in a vector, remove it
  dropLabel : (xs : OrdHeader k o) -> (loc : OrdLabel l xs) -> OrdHeader k o
  dropLabel (_ :: xs) Here          = xs
  dropLabel (x :: xs) (There later) = x :: dropLabel xs later

  ||| Update a value in the list given it's location and an update function
  updateLabel : (xs : OrdHeader k o) -> (loc : OrdLabel l xs) ->
                (new : Type) -> OrdHeader k o
  updateLabel ((x, old) :: xs) Here          new = (x, new) :: xs
  updateLabel (x :: xs)        (There later) new = x :: updateLabel xs later new

  ||| Decide whether a key is in a vector or not
  decLabel : DecEq k => (l : k) -> (xs : OrdHeader k o) -> Dec (OrdLabel l xs)
  decLabel _   [] = No (\pf => absurd pf)
  decLabel k ((k', v') :: xs) with (decEq k k')
    | (Yes prf) = rewrite prf in Yes Here
    | (No notHere) with (decLabel k xs)
      | Yes loc     = Yes (There loc)
      | No notThere = No (\loc => case loc of
                                       Here        => absurd (notHere Refl)
                                       There later => absurd (notThere later))

namespace Label

  data Label : (k : l) -> (xs : Header l) -> Type where
    L : Ord l => {k : l} -> OrdLabel k xs -> Label k (H xs)

namespace OrdRow

  ||| Proof that a key value pair is part of a vector
  data OrdRow : (l : k) -> (ty : Type) -> OrdHeader k o -> Type where
    Here  :                          OrdRow l ty ((l, ty) :: xs)
    There : (later : OrdRow l ty xs) -> OrdRow l ty (x::xs)

  labelFromOrdRow : OrdRow k ty xs -> OrdLabel k xs
  labelFromOrdRow Here          = Here
  labelFromOrdRow (There later) = There (labelFromOrdRow later)

  Uninhabited (OrdRow k v []) where
    uninhabited Here      impossible
    uninhabited (There _) impossible

  ||| Given a proof that an element is in a vector, remove it
  dropOrdRow : (xs : OrdHeader k o) -> (loc : OrdRow l ty xs) -> OrdHeader k o
  dropOrdRow xs = dropLabel xs . labelFromOrdRow

  ||| Update a value in the list given it's location and an update function
  updateOrdRow : (xs : OrdHeader k o) -> (loc : OrdRow l old xs) -> (new : Type) ->
              OrdHeader k o
  updateOrdRow xs loc new = updateLabel xs (labelFromOrdRow loc) new

  findInsertOrdRow : (l : k) -> (xs : OrdHeader k o) -> OrdRow l ty (insert (l,ty) xs)
  findInsertOrdRow l [] = Here
  findInsertOrdRow l ((kx, vx) :: xs) with (l < kx)
    | True = Here
    | False = There (findInsertOrdRow l xs)

  dropInsertInv : (l : k) -> (ty : Type) -> (xs : OrdHeader k o) ->
                  dropOrdRow (insert (l, ty) xs) (findInsertOrdRow l xs) = xs
  dropInsertInv l ty [] = Refl
  dropInsertInv l ty ((kx,vx) :: xs) with (l < kx)
    | True = Refl
    | False = cong (dropInsertInv l ty xs)

namespace Fresh

  data Fresh : (l : label) -> (xs : OrdHeader label o) -> Type where
    Nil  : Fresh l []
    (::) : Not (l = l') -> Fresh l xs -> Fresh l ((l',ty') :: xs)

  freshCantBeLabel : Fresh l xs -> OrdLabel l xs -> Void
  freshCantBeLabel (f :: fresh) Here = f Refl
  freshCantBeLabel (f :: fresh) (There later) = freshCantBeLabel fresh later

  %name Fresh fresh, prf, new

  decFresh : DecEq label => (l : label) -> (xs : OrdHeader label o) -> Dec (Fresh l xs)
  decFresh l [] = Yes []
  decFresh l ((l', ty) :: xs) with (decEq l l')
    | (Yes prf) = No (\ (freshHead :: _) => freshHead prf)
    | (No freshHere) with (decFresh l xs)
      | (Yes freshThere) = Yes (freshHere :: freshThere)
      | (No f) = No (\ (_ :: freshTail) => f freshTail)

  IsFresh : DecEq label => (l : label) -> (xs : OrdHeader label o) -> Type
  IsFresh l xs = IsYes (decFresh l xs)


  isFreshFromEvidence : DecEq label => {l : label} -> (prf : Fresh l xs) -> IsFresh l xs
  isFreshFromEvidence prf {l} {xs} with (decFresh l xs)
    | (Yes _) = SoTrue
    | (No contra) = absurd (contra prf)

  tailIsFresh : DecEq label => {l : label} -> IsFresh l (x :: xs) -> IsFresh l xs
  tailIsFresh x = case getProof x of (f :: fresh) => isFreshFromEvidence fresh

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

  toHList : Record k header -> HList (toList header)
  toHList (Rec xs _) = toHList xs

  implementation
  Eq (HList (toList header)) => Eq (Record k header) where
    (==) xs ys = toHList xs == toHList ys
    (/=) xs ys = toHList xs /= toHList ys

