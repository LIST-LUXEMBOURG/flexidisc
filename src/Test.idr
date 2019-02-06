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


namespace OrdHeader

  data OrdHeader : (k : Type) -> (Ord k) -> Type where
    Nil  : OrdHeader k o
    (::) : (k, Type) -> OrdHeader k o -> OrdHeader k o

  insert : (k, Type) -> OrdHeader k o -> OrdHeader k o
  insert x []= [x]
  insert (k, v) ((k', v') :: xs) with (k < k')
    | False = (k',v') :: (insert (k, v) xs)
    | True  = (k,v)   :: (k',v') :: xs

  header : (o : Ord k) => List (k, Type) -> OrdHeader k o
  header = foldl (flip insert) Nil

namespace Header

  data Header : (k : Type) -> Type where
    H : (o : Ord k) => OrdHeader k o -> Header k

  Nil : Ord k => Header k
  Nil = H []

  (::) : (k, Type) -> Header k -> Header k
  (::) x (H h) = H (insert x h)

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


namespace Label

  data Label : (k : l) -> (xs : OrdHeader l o) -> Type where
    Here : Label k ((k,v)::xs)
    There : (later : Label k xs) -> Label k (x::xs)

  %name Label lbl, loc, prf, e, elem

  atLabel : (xs : OrdHeader l o) -> (loc : Label k xs) -> Type
  atLabel ((_, v) :: _) Here = v
  atLabel (_ :: xs) (There later) = atLabel xs later

  Uninhabited (Label k []) where
    uninhabited Here      impossible
    uninhabited (There _) impossible

  ||| Given a proof that an element is in a vector, remove it
  dropLabel : (xs : OrdHeader k o) -> (loc : Label l xs) -> OrdHeader k o
  dropLabel (_ :: xs) Here          = xs
  dropLabel (x :: xs) (There later) = x :: dropLabel xs later

  ||| Update a value in the list given it's location and an update function
  updateLabel : (xs : OrdHeader k o) -> (loc : Label l xs) ->
                (new : Type) -> OrdHeader k o
  updateLabel ((x, old) :: xs) Here          new = (x, new) :: xs
  updateLabel (x :: xs)        (There later) new = x :: updateLabel xs later new

  ||| Decide whether a key is in a vector or not
  decLabel : DecEq k => (l : k) -> (xs : OrdHeader k o) -> Dec (Label l xs)
  decLabel _   [] = No (\pf => absurd pf)
  decLabel k ((k', v') :: xs) with (decEq k k')
    | (Yes prf) = rewrite prf in Yes Here
    | (No notHere) with (decLabel k xs)
      | Yes loc     = Yes (There loc)
      | No notThere = No (\loc => case loc of
                                       Here        => absurd (notHere Refl)
                                       There later => absurd (notThere later))

namespace Row

  ||| Proof that a key value pair is part of a vector
  data Row : (l : k) -> (ty : Type) -> OrdHeader k o -> Type where
    Here  :                          Row l ty ((l, ty) :: xs)
    There : (later : Row l ty xs) -> Row l ty (x::xs)

  labelFromRow : Row k ty xs -> Label k xs
  labelFromRow Here          = Here
  labelFromRow (There later) = There (labelFromRow later)

  Uninhabited (Row k v []) where
    uninhabited Here      impossible
    uninhabited (There _) impossible

  ||| Given a proof that an element is in a vector, remove it
  dropRow : (xs : OrdHeader k o) -> (loc : Row l ty xs) -> OrdHeader k o
  dropRow xs = dropLabel xs . labelFromRow

  ||| Update a value in the list given it's location and an update function
  updateRow : (xs : OrdHeader k o) -> (loc : Row l old xs) -> (new : Type) ->
              OrdHeader k o
  updateRow xs loc new = updateLabel xs (labelFromRow loc) new

  findInsertRow : (l : k) -> (xs : OrdHeader k o) -> Row l ty (insert (l,ty) xs)
  findInsertRow l [] = Here
  findInsertRow l ((kx, vx) :: xs) with (l < kx)
    | True = Here
    | False = There (findInsertRow l xs)

  dropInsertInv : (l : k) -> (ty : Type) -> (xs : OrdHeader k o) ->
                  dropRow (insert (l, ty) xs) (findInsertRow l xs) = xs
  dropInsertInv l ty [] = Refl
  dropInsertInv l ty ((kx,vx) :: xs) with (l < kx)
    | True = Refl
    | False = cong (dropInsertInv l ty xs)

namespace Fresh

  data Fresh : (l : label) -> (xs : OrdHeader label o) -> Type where
    Nil  : Fresh l []
    (::) : Not (l = l') -> Fresh l xs -> Fresh l ((l',ty') :: xs)

  freshCantBeLabel : Fresh l xs -> Label l xs -> Void
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
                         Nub xs -> (ePre : Label k xs) -> Fresh k (dropLabel xs ePre)
  removeFromNubIsFresh (yes :: isnub) Here = getProof yes
  removeFromNubIsFresh (yes :: isnub) (There later) =
    (\p => freshCantBeLabel (getProof yes) (rewrite (sym p) in later)) :: removeFromNubIsFresh isnub later

  dropPreservesFresh : Fresh l xs -> Fresh l (dropLabel xs e)
  dropPreservesFresh (f :: fresh) {e = Here} = fresh
  dropPreservesFresh (f :: fresh) {e = (There e)} = f :: dropPreservesFresh fresh

  dropPreservesNub : Nub xs -> (loc : Label l xs) -> Nub (dropLabel xs loc)
  dropPreservesNub (yes :: x) Here = x
  dropPreservesNub (yes :: x) (There later) =
    isFreshFromEvidence (dropPreservesFresh (getProof yes)) :: dropPreservesNub x later



namespace Permute

  ||| Proof that a `Vect` is a permutation of another vect
  data Permute : (xs : OrdHeader k o) ->
                 (ys : OrdHeader k o) ->
                 Type where
    Empty : Permute [] []
    Keep  : (e : Row k ty ys) -> Permute xs (dropRow ys e) ->
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
    Keep (findInsertRow l xs) 
         (rewrite dropInsertInv l ty xs in (permuteRefl xs))

  permutePreservesFresh :  Permute ys xs -> Fresh k xs -> Fresh k ys
  permutePreservesFresh Empty fresh = fresh
  permutePreservesFresh (Keep e perm) fresh =
    (\p => freshCantBeLabel fresh (rewrite p in labelFromRow e)) ::
    permutePreservesFresh perm (dropPreservesFresh fresh)

  isNubFromPermute : Permute xs ys -> Nub ys -> Nub xs
  isNubFromPermute Empty [] = []
  isNubFromPermute (Keep e perm) pf@(p::_) =
    isFreshFromEvidence
      (permutePreservesFresh perm (removeFromNubIsFresh pf (labelFromRow e)))
    :: isNubFromPermute perm (dropPreservesNub pf (labelFromRow e))

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
