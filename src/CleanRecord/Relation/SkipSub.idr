module CleanRecord.Relation.SkipSub

import CleanRecord.Elem.Label
import CleanRecord.IsNo
import CleanRecord.Nub

import CleanRecord.Relation.NegSub

import Data.List

%default total
%access public export

||| Charectarise a subset by giving the keys that are removed
data SkipSub : (keys : List key) ->
              (sub : List (key, value)) ->
              (initial : List (key, value)) ->
               Type where
  Empty : SkipSub [] [] []
  Skip  : (e : Label k initial) -> SkipSub keys sub (dropLabel initial e) ->
          SkipSub (k::keys) sub initial
  Keep  : SkipSub keys sub initial -> SkipSub keys ((k, v) :: sub) ((k, v) :: initial)

||| An empty `List` is an ordered subset of any `List`
subEmpty' : (xs : List (key, value)) -> SkipSub (map Basics.fst xs) [] xs
subEmpty' [] = Empty
subEmpty' ((k, v) :: xs) = Skip Here (subEmpty' xs)

||| An empty `List` is an ordered subset of any `List`
subEmpty : SkipSub (map Basics.fst xs) [] xs
subEmpty {xs} = subEmpty' xs

||| A `List` is an ordered subset of itself
subRefl' : (xs : List (key, value)) -> SkipSub [] xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep (subRefl' xs)

||| A `List` is an ordered subset of itself
subRefl :  SkipSub [] xs xs
subRefl {xs} = subRefl' xs

toNegSub : SkipSub keep sub initial -> NegSub sub initial
toNegSub Empty = Empty
toNegSub (Skip loc sub) = Skip loc (toNegSub sub)
toNegSub (Keep sub) = Keep (toNegSub sub)
