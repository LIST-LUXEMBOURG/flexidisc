module CleanRecord.SubKey

import CleanRecord.Row
import CleanRecord.IsNo
import CleanRecord.Nub
import CleanRecord.Sub

import Data.Vect

%default total


public export
data SubKey : (keys : Vect n key) ->
               (sub : Vect n (key, value)) ->
               (initial : Vect m (key, value)) ->
               Type where
  Empty : SubKey [] [] []
  Skip  : SubKey keys sub initial -> SubKey keys sub ((k, v) :: initial)
  Keep  : (e : Row k v initial) -> SubKey keys sub (dropRow initial e) ->
          SubKey (k :: keys) ((k,v)::sub) initial

public export
subEmpty' : (xs : Vect n (key, value)) -> SubKey [] [] xs
subEmpty' [] = Empty
subEmpty' ((k, v) :: xs) = Skip (subEmpty' xs)

public export
subEmpty : SubKey [] [] xs
subEmpty {xs} = subEmpty' xs

public export
subRefl' : (xs : Vect n (key, value)) -> SubKey (map Basics.fst xs) xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep Here (subRefl' xs)

public export
subRefl :  SubKey (map Basics.fst xs) xs xs
subRefl {xs} = subRefl' xs

public export
toSub : SubKey keep sub initial -> Sub sub initial
toSub Empty = Empty
toSub (Skip x) = Skip (toSub x)
toSub (Keep e x) = Keep e (toSub x)
