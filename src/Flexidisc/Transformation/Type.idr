module Flexidisc.Transformation.Type

import Flexidisc.OrdHeader
import Flexidisc.RecordContent
import Flexidisc.TaggedValue

import Control.Monad.Identity

%default total
%access export

infixr 9 :->

public export
data MapValue = (:->) Type Type

public export
data MapValuesM : (m : Type -> Type) -> (k : Type) -> (o : Ord k) ->
                  (header : OrdList k o MapValue) -> Type where
    Nil  : (o : Ord k) => MapValuesM m k o []
    (::) : TaggedValue l (s -> m t) -> MapValuesM m k o header ->
           MapValuesM m k o ((l, s :-> t) :: header)

public export
MapValues :  (k : Type) -> (o : Ord k) -> OrdList k o MapValue -> Type
MapValues = MapValuesM id

insert : TaggedValue k' (s -> m t) -> MapValuesM m k o header ->
         MapValuesM m k o (insert (k', s :-> t) header)
insert x [] = [x]
insert (k' := v) ((kx := vx) :: xs') with (k' < kx)
  | False = (kx := vx) :: (insert (k' := v) xs')
  | True  = (k' := v) :: (kx := vx) :: xs'

public export
toLabels : OrdList k o MapValue -> List k
toLabels [] = []
toLabels ((k, s :-> t) :: xs) = k :: toLabels xs

public export
toSource : OrdList k o MapValue -> OrdHeader k o
toSource [] = []
toSource ((k, s :-> t) :: xs) = (k, s) :: toSource xs

public export
toTarget : OrdList k o MapValue -> OrdHeader k o
toTarget [] = []
toTarget ((k, s :-> t) :: xs) = (k, t) :: toTarget xs

mapRecord : (o : Ord k) =>
            (trans : MapValuesM m k o mapper) ->
            (xs : RecordContent k o (toSource mapper)) ->
            RecordContentM m k o (toTarget mapper)
mapRecord [] [] = []
mapRecord (k := f :: fs) (k := x :: xs) = k := f x :: mapRecord fs xs

traverseRecord : (o : Ord k, Applicative m) =>
                 (trans : MapValuesM m k o mapper) ->
                 (xs : RecordContent k o (toSource mapper)) ->
                 m (RecordContent k o (toTarget mapper))
traverseRecord [] [] = pure []
traverseRecord ((k := f) :: fs) ((k := x) :: xs) =
  mapHead k <$> f x <*> traverseRecord fs xs
    where
      mapHead k' x' xs' = k' := x' :: xs'

patchRecord : (DecEq k, Applicative m) =>
              (trans : MapValuesM m k o mapper) ->
              (xs : RecordContent k o header) ->
              (prf : Sub (toSource mapper) header) ->
              m (RecordContent k o (patch (toTarget mapper) header))
patchRecord trans xs {prf} =
  (\p => p |> xs) <$> traverseRecord trans (project xs prf)

patchRecord' : DecEq k =>
               (trans : MapValues k o mapper) ->
               (xs : RecordContent k o header) ->
               (prf : Sub (toSource mapper) header) ->
               RecordContent k o (patch (toTarget mapper) header)
patchRecord' trans xs {prf} =
  mapRecord trans (project xs prf) |> xs
