module Example.Stream

import Data.Fin
import Flexidisc.Record

RecordMPair : (Type -> Type) -> Type
RecordMPair m = RecordM m (Fin 2) [FZ ::: Nat, FS FZ ::: Char]

test : RecordMPair Stream
test = [0 := [1..], 1 := pure 'c']

someOfTest : List (RecordMPair Basics.id)
someOfTest = take 10 (sequence test)
