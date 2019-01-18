module CleanRecord.SkipSub

import CleanRecord.Row
import CleanRecord.IsNo
import CleanRecord.Nub
import CleanRecord.OrdSub
import CleanRecord.Sub

import Data.Vect

%default total


public export
data SkipSub : (keys : Vect k key) ->
              (sub : Vect n (key, value)) ->
              (initial : Vect m (key, value)) ->
               Type where
  Empty : SkipSub [] [] []
  Skip  : SkipSub keys sub initial -> SkipSub (k::keys) sub ((k, v) :: initial)
  Keep  : (e : Row k v initial) -> SkipSub keys sub (dropRow initial e) ->
          SkipSub keys ((k,v)::sub) initial

public export
subEmpty' : (xs : Vect n (key, value)) -> SkipSub (map Basics.fst xs) [] xs
subEmpty' [] = Empty
subEmpty' ((k, v) :: xs) = Skip (subEmpty' xs)

public export
subEmpty : SkipSub (map Basics.fst xs) [] xs
subEmpty {xs} = subEmpty' xs

public export
subRefl' : (xs : Vect n (key, value)) -> SkipSub [] xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep Here (subRefl' xs)

public export
subRefl :  SkipSub [] xs xs
subRefl {xs} = subRefl' xs

public export
toSub : SkipSub keep sub initial -> Sub sub initial
toSub Empty = Empty
toSub (Skip x) = Skip (toSub x)
toSub (Keep e x) = Keep e (toSub x)
