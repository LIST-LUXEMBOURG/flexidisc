module CleanRecord.Relation.SubWithKeys

import CleanRecord.Row
import CleanRecord.IsNo
import CleanRecord.Nub
import CleanRecord.Relation.OrdSub
import CleanRecord.Relation.Sub

import Data.List

%default total
%access public export

||| A `Sub` with an explicit parameter for the list of keys that are present in the Sub
data SubWithKeys : (keys : List key) ->
              (sub : List (key, value)) ->
              (initial : List (key, value)) ->
               Type where
  Empty : SubWithKeys [] [] []
  Skip  : SubWithKeys keys sub initial -> SubWithKeys keys sub ((k, v) :: initial)
  Keep  : (e : Row k v initial) -> SubWithKeys keys sub (dropRow initial e) ->
          SubWithKeys (k :: keys) ((k,v)::sub) initial

||| An empty `List` is a subset of any `List`
subEmpty' : (xs : List (key, value)) -> SubWithKeys [] [] xs
subEmpty' [] = Empty
subEmpty' ((k, v) :: xs) = Skip (subEmpty' xs)

||| An empty `List` is a subset of any `List`
subEmpty : SubWithKeys [] [] xs
subEmpty {xs} = subEmpty' xs

||| A `List` is a subset of itself
subRefl' : (xs : List (key, value)) -> SubWithKeys (map Basics.fst xs) xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep Here (subRefl' xs)

||| A `List` is a subset of itself
subRefl :  SubWithKeys (map Basics.fst xs) xs xs
subRefl {xs} = subRefl' xs

||| Build a `Sub` from a SubWithKeys
toSub : SubWithKeys keep sub initial -> Sub sub initial
toSub Empty = Empty
toSub (Skip x) = Skip (toSub x)
toSub (Keep e x) = Keep e (toSub x)
