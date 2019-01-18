module CleanRecord.KeepSub

import CleanRecord.Row
import CleanRecord.IsNo
import CleanRecord.Nub
import CleanRecord.OrdSub
import CleanRecord.Sub

import Data.Vect

%default total


public export
data KeepSub : (keys : Vect n key) ->
              (sub : Vect n (key, value)) ->
              (initial : Vect m (key, value)) ->
               Type where
  Empty : KeepSub [] [] []
  Skip  : KeepSub keys sub initial -> KeepSub keys sub ((k, v) :: initial)
  Keep  : (e : Row k v initial) -> KeepSub keys sub (dropRow initial e) ->
          KeepSub (k :: keys) ((k,v)::sub) initial

public export
subEmpty' : (xs : Vect n (key, value)) -> KeepSub [] [] xs
subEmpty' [] = Empty
subEmpty' ((k, v) :: xs) = Skip (subEmpty' xs)

public export
subEmpty : KeepSub [] [] xs
subEmpty {xs} = subEmpty' xs

public export
subRefl' : (xs : Vect n (key, value)) -> KeepSub (map Basics.fst xs) xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep Here (subRefl' xs)

public export
subRefl :  KeepSub (map Basics.fst xs) xs xs
subRefl {xs} = subRefl' xs

public export
toSub : KeepSub keep sub initial -> Sub sub initial
toSub Empty = Empty
toSub (Skip x) = Skip (toSub x)
toSub (Keep e x) = Keep e (toSub x)
