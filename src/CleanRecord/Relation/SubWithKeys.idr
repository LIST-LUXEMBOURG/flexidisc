module CleanRecord.Relation.SubWithKeys

import CleanRecord.Row
import CleanRecord.IsNo
import CleanRecord.Nub
import CleanRecord.Relation.OrdSub
import CleanRecord.Relation.Sub

import Data.Vect

%default total

||| A `Sub` with an explicit parameter for the list of keys that are present in the Sub
public export
data SubWithKeys : (keys : Vect n key) ->
              (sub : Vect n (key, value)) ->
              (initial : Vect m (key, value)) ->
               Type where
  Empty : SubWithKeys [] [] []
  Skip  : SubWithKeys keys sub initial -> SubWithKeys keys sub ((k, v) :: initial)
  Keep  : (e : Row k v initial) -> SubWithKeys keys sub (dropRow initial e) ->
          SubWithKeys (k :: keys) ((k,v)::sub) initial

||| An empty `Vect` is a subset of any `Vect`
public export
subEmpty' : (xs : Vect n (key, value)) -> SubWithKeys [] [] xs
subEmpty' [] = Empty
subEmpty' ((k, v) :: xs) = Skip (subEmpty' xs)

||| An empty `Vect` is a subset of any `Vect`
public export
subEmpty : SubWithKeys [] [] xs
subEmpty {xs} = subEmpty' xs

||| A `Vect` is a subset of itself
public export
subRefl' : (xs : Vect n (key, value)) -> SubWithKeys (map Basics.fst xs) xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep Here (subRefl' xs)

||| A `Vect` is a subset of itself
public export
subRefl :  SubWithKeys (map Basics.fst xs) xs xs
subRefl {xs} = subRefl' xs

||| Build a `Sub` from a SubWithKeys
public export
toSub : SubWithKeys keep sub initial -> Sub sub initial
toSub Empty = Empty
toSub (Skip x) = Skip (toSub x)
toSub (Keep e x) = Keep e (toSub x)
