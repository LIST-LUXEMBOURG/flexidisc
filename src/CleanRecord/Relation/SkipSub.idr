module CleanRecord.Relation.SkipSub

import CleanRecord.Label
import CleanRecord.IsNo
import CleanRecord.Nub

import CleanRecord.Relation.NegSub
import CleanRecord.Relation.OrdSub

import Data.Vect

%default total

||| Charectarise a subset by giving the keys that are removed
public export
data SkipSub : (keys : Vect k key) ->
              (sub : Vect n (key, value)) ->
              (initial : Vect m (key, value)) ->
               Type where
  Empty : SkipSub [] [] []
  Skip  : (e : Label k initial) -> SkipSub keys sub (dropLabel initial e) ->
          SkipSub (k::keys) sub initial
  Keep  : SkipSub keys sub initial -> SkipSub keys ((k, v) :: sub) ((k, v) :: initial)

||| An empty `Vect` is an ordered subset of any `Vect`
public export
subEmpty' : (xs : Vect n (key, value)) -> SkipSub (map Basics.fst xs) [] xs
subEmpty' [] = Empty
subEmpty' ((k, v) :: xs) = Skip Here (subEmpty' xs)

||| An empty `Vect` is an ordered subset of any `Vect`
public export
subEmpty : SkipSub (map Basics.fst xs) [] xs
subEmpty {xs} = subEmpty' xs

||| A `Vect` is an ordered subset of itself
public export
subRefl' : (xs : Vect n (key, value)) -> SkipSub [] xs xs
subRefl' [] = Empty
subRefl' ((k, v) :: xs) = Keep (subRefl' xs)

||| A `Vect` is an ordered subset of itself
public export
subRefl :  SkipSub [] xs xs
subRefl {xs} = subRefl' xs

public export
toNegSub : SkipSub keep sub initial -> NegSub sub initial
toNegSub Empty = Empty
toNegSub (Skip loc sub) = Skip loc (toNegSub sub)
toNegSub (Keep sub) = Keep (toNegSub sub)
