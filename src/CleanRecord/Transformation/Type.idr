module CleanRecord.Transformation.Type

import CleanRecord.OrdHeader
import CleanRecord.RecordContent
import CleanRecord.TaggedValue

import Control.Monad.Identity

%default total
%access export

infixr 9 :->

public export
data MapValue = (:->) Type Type

public export
data MapValuesM : (m : Type -> Type) -> (k : Type) -> (o : Ord k) ->
                  (header : OrdList k MapValue o) -> Type where
    Nil  : (o : Ord k) => MapValuesM m k o []
    (::) : TaggedValue l (s -> m t) -> MapValuesM m k o header ->
           MapValuesM m k o ((l, s :-> t) :: header)

public export
MapValues :  (k : Type) -> (o : Ord k) -> OrdList k MapValue o -> Type
MapValues = MapValuesM Identity

insert : TaggedValue k' (s -> m t) -> MapValuesM m k o header ->
         MapValuesM m k o (insert (k', s :-> t) header)
insert x [] = [x]
insert (k' := v) ((kx := vx) :: xs') with (k' < kx)
  | False = (kx := vx) :: (insert (k' := v) xs')
  | True  = (k' := v) :: (kx := vx) :: xs'

public export
toLabels : OrdList k MapValue o -> List k
toLabels [] = []
toLabels ((k, s :-> t) :: xs) = k :: toLabels xs

public export
toSource : OrdList k MapValue o -> OrdHeader k o
toSource [] = []
toSource ((k, s :-> t) :: xs) = (k, s) :: toSource xs

public export
toTarget : OrdList k MapValue o -> OrdHeader k o
toTarget [] = []
toTarget ((k, s :-> t) :: xs) = (k, t) :: toTarget xs

mapRecordM : (o : Ord k, Applicative m) =>
             (trans : MapValuesM m k o mapper) ->
             (xs : RecordContent k o (toSource mapper)) ->
             m (RecordContent k o (toTarget mapper))
mapRecordM [] [] = pure []
mapRecordM ((k := f) :: fs) ((k := x) :: xs) =
  mapHead k <$> f x <*> mapRecordM fs xs
    where
      mapHead k' x' xs' = k' := x' :: xs'

patchM : (DecEq k, Applicative m) =>
         (trans : MapValuesM m k o mapper) ->
         (xs : RecordContent k o header) ->
         (prf : Sub (toSource mapper) header) ->
         m (RecordContent k o (patch (toTarget mapper) header))
patchM trans xs {prf} =
  (\p => p |> xs) <$> mapRecordM trans (project xs prf)
