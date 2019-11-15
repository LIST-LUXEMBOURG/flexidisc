module Flexidisc.Record.Transformation

import Flexidisc.Record
import Flexidisc.RecordContent
import Flexidisc.OrdList.Disjoint
import Flexidisc.OrdList.Nub
import public Flexidisc.Transformation.Type
import public Flexidisc.Transformation.TransHeader

import public Control.Monad.Identity

%default total
%access export

||| A list of transformation of tagged values.
||| Its purpose is to apply several transformation on different fields
||| simultaneously.
data TransformationM : (m : Type -> Type) -> (k : Type) ->
                       (header : TransHeader k) -> Type where
  Trans : (o : Ord k) =>
          (values : MapValuesM m k o header) ->
          (nubProof : Nub header) ->
          TransformationM m k (T header)

public export
Transformation : (k : Type) -> (header : TransHeader k) -> Type
Transformation = TransformationM id

||| Monomorphic `id` to help inference
transM : (m : Type -> Type) -> TransformationM m k header -> TransformationM m k header
transM _ = id

||| Monomorphic `id` to help inference
trans : TransformationM Identity k header -> TransformationM Identity k header
trans = id

||| The empty record
Nil : Ord k => TransformationM m k []
Nil = Trans [] []

||| Insert a new row in a record
(::) : (DecEq k, Ord k) => TaggedValue k' (s -> m t) -> TransformationM m k header ->
       {default SoTrue fresh : IsFresh k' header} ->
       TransformationM m k ((k', s :-> t) :: header)
(::) x (Trans xs isnub) {fresh} =
  Trans (insert x xs) (freshInsert (getProof fresh) isnub)

transPreservesFresh : Ord k => (xs : OrdList k o MapValue) -> (y : Fresh l (toSource xs)) -> Fresh l (toTarget xs)
transPreservesFresh [] y = y
transPreservesFresh ((k, s :-> t) :: xs) (f :: fresh) = f :: transPreservesFresh xs fresh

transPreservesNub : (header : OrdList k o MapValue) -> Nub (toSource header) -> Nub (toTarget header)
transPreservesNub [] xs = xs
transPreservesNub ((l, s :-> t) :: xs) (y::ys) = transPreservesFresh xs y :: transPreservesNub xs ys

||| Map all the field of a record
mapRecord : (trans : TransformationM m k mapper) ->
            (xs : Record k (toSource mapper)) ->
            RecordM m k (toTarget mapper)
mapRecord (Trans trans nubT) (Rec xs nubXS) {mapper = T mapper} =
  Rec (mapRecord trans xs) (transPreservesNub mapper nubXS)

||| Map all the field of a record
traverseRecord : Applicative m =>
                 (trans : TransformationM m k mapper) ->
                 (xs : Record k (toSource mapper)) ->
                 m (Record k (toTarget mapper))
traverseRecord (Trans trans nubT) (Rec xs nubXS) {mapper = T mapper} =
  map (flip Rec (transPreservesNub mapper nubXS)) (traverseRecord trans xs)

||| Map all the field of a record
traverseRecord' : (trans : Transformation k mapper) ->
                  (xs : Record k (toSource mapper)) ->
                  Record k (toTarget mapper)
traverseRecord' = mapRecord


||| Create a record of Maybe type, with the values of the initial record,
||| if defined, or with `Nothing` if the field is not defined.
optional : DecEq k => (post : Header k) ->
           (xs : Record k header) ->
           {auto prf : HereOrNot post header} ->
           {default SoTrue postNub : IsNub post} ->
           RecordM Maybe k post
optional _ (Rec xs nubXS) {prf = HN prf} {postNub} =
  Rec (optional xs prf) (getProof postNub)

||| Change the effect
hoist : (f: {a : _} -> m a -> n a) -> (xs : RecordM m k header) -> RecordM n k header
hoist f (Rec xs nubXS) = Rec (hoist f xs) nubXS

||| Perform a `Record` transformation under the `Identity` Monad
withIdentity : (RecordM Identity k pre -> RecordM Identity k post) ->
               Record k pre -> Record k post
withIdentity f = hoist runIdentity . f . hoist Id

||| lift fields of a Record
lift : (f: {a : _} -> a -> m a) -> (xs : Record k header) -> RecordM m k header
lift = hoist

||| extract an effect from a record
sequence : Applicative m => (xs : RecordM m k header) -> m (Record k header)
sequence (Rec xs nubXS) = flip Rec nubXS <$> sequence xs

||| embed the effect in the values, directly
unlift : RecordM m k header -> Record k (map m header)
unlift (Rec values nubProof) = Rec (unlift values) (mapValuesPreservesNub nubProof)

-- Foldmap

public export
data RecordFunc : (required : Header k) ->
                  (optional : Header k) ->
                  (result : Type) -> Type where
  Func : (Record k required -> RecordM Maybe k opt -> a) ->
         RecordFunc required opt a

||| Apply a function on a known set of data
foldRecord : (Ord k, DecEq k) =>
             RecordFunc required opt a ->
             Record k header ->
             {auto optNub : IsNub opt} ->
             {auto decomp : Decomp required opt header} ->
             a
foldRecord (Func f) xs {opt} {decomp = D sub op} {optNub} =
  f (project xs) (optional opt xs {postNub = optNub})



||| Map a subset of a record
patchRecord : (DecEq k, Applicative m) =>
              (trans : TransformationM m k mapper) ->
              (xs : Record k header) ->
              {auto prf : Sub (toSource mapper) header} ->
              m (Record k (patch (toTarget mapper) header))
patchRecord (Trans trans nubT) (Rec xs nubXS) {prf = S prf} {mapper = T mapper} = let
  nubProof = disjointNub diffIsDisjoint
                         (isNubFromSub diffIsSub nubXS)
                         (transPreservesNub mapper (isNubFromSub prf nubXS))
  in map (flip Rec nubProof) (patchRecord trans xs prf)

||| Map a subset of a record
patchRecord' : DecEq k =>
               (trans : Transformation k mapper) ->
               (xs : Record k header) ->
               {auto prf : Sub (toSource mapper) header} ->
               Record k (patch (toTarget mapper) header)
patchRecord' (Trans trans nubT) (Rec xs nubXS) {prf = S prf} {mapper = T mapper} = let
  nubProof = disjointNub diffIsDisjoint
                         (isNubFromSub diffIsSub nubXS)
                         (transPreservesNub mapper (isNubFromSub prf nubXS))
  in (flip Rec nubProof) (patchRecord' trans xs prf)

||| Apply a modifier Record to a record
(<**>) : RecordM (endoM m n) k header -> RecordM m k header -> RecordM n k header
(<**>) (Rec fs _) (Rec xs nubXS) = Rec (fs <**> xs) nubXS

-- Operators

keepIf : (Alternative m, Applicative m) => (a -> Bool) -> a -> m a
keepIf f x = map (const x) (guard (f x))

is : (Eq a, Alternative m, Applicative m) => a -> a -> m a
is expected = keepIf (== expected)

isnot : (Eq a, Alternative m, Applicative m) => a -> a -> m a
isnot expected = keepIf (/= expected)
