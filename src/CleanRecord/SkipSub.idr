module CleanRecord.SkipSub

import CleanRecord.Label
import CleanRecord.IsNo
import CleanRecord.NegSub
import CleanRecord.Nub
import CleanRecord.OrdSub

import Data.Vect

%default total


public export
data SkipSub : (keys : Vect k key) ->
              (sub : Vect n (key, value)) ->
              (initial : Vect m (key, value)) ->
               Type where
  Empty : SkipSub [] [] []
  Skip  : (e : Label k initial) -> SkipSub keys sub (dropLabel initial e) ->
          SkipSub (k::keys) sub initial
  Keep  : SkipSub keys sub initial -> SkipSub keys ((k, v) :: sub) ((k, v) :: initial)

public export
subEmpty' : (xs : Vect n (key, value)) -> SkipSub (map Basics.fst xs) [] xs
subEmpty' [] = Empty
subEmpty' ((k, v) :: xs) = Skip Here (subEmpty' xs)

public export
subEmpty : SkipSub (map Basics.fst xs) [] xs
subEmpty {xs} = subEmpty' xs

public export
subRefl' : (xs : Vect n (key, value)) -> SkipSub [] xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep (subRefl' xs)

public export
subRefl :  SkipSub [] xs xs
subRefl {xs} = subRefl' xs

public export
toNegSub : SkipSub keep sub initial -> NegSub sub initial
toNegSub Empty = Empty
toNegSub (Skip loc sub) = Skip loc (toNegSub sub)
toNegSub (Keep sub) = Keep (toNegSub sub)
