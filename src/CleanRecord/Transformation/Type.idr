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
                  OrdList k MapValue o -> Type where
    Nil  : (o : Ord k) => MapValuesM m k o []
    (::) : TaggedValue l (s -> m t) -> MapValuesM m k o header ->
           MapValuesM m k o ((l, s :-> t) :: header)

public export
MapValues :  (k : Type) -> (o : Ord k) -> OrdList k MapValue o -> Type
MapValues = MapValuesM Identity

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

excactMapRecordM : (o : Ord k, Monad m) =>
             (selector : MapValuesM m k o mapper) ->
             (xs : RecordContent k o (toSource mapper)) ->
             m (RecordContent k o (toTarget mapper))
excactMapRecordM [] xs = pure xs
excactMapRecordM ((k := f) :: fs) ((k := x) :: xs) = do
  x' <- f x
  map ((k := x') ::) (excactMapRecordM fs xs)

