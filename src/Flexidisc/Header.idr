module Flexidisc.Header

import public Flexidisc.Dec.IsYes
import public Flexidisc.Header.Label
import public Flexidisc.Header.Row
import public Flexidisc.Header.Sub
import public Flexidisc.Header.Type

import Flexidisc.OrdHeader

%default total
%access public export

data CompWithKeys : (List k) -> (xs : Header k) -> (ys : Header k) -> Type where
  S : {xs : OrdHeader k o} -> {ys : OrdHeader k o} ->
      CompWithKeys keys xs ys -> CompWithKeys keys (H xs) (H ys)

data Disjoint : (xs : Header k) -> (ys : Header k) -> Type where
  D : {xs : OrdHeader k o} -> {ys : OrdHeader k o} ->
      Disjoint xs ys -> Disjoint (H xs) (H ys)


data Fresh : (l : label) -> (xs : Header' label a) -> Type where
  F : {xs : OrdList k o a} -> Fresh l xs -> Fresh l (H xs)

%name Header.Fresh fresh, prf, new

mapType : (f : Type -> Type) -> Header k -> Header k
mapType f (H xs) = H (map f xs)

decFresh : (DecEq label) => (l : label) -> (xs : Header' label a) ->
           Dec (Fresh l xs)
decFresh l (H xs) with (decFresh l xs)
  | (Yes prf) = Yes (F prf)
  | (No contra) = No (\(F x) => contra x)

IsFresh : (DecEq label) => (l : label) -> (xs : Header' label a) -> Type
IsFresh l xs = IsYes (decFresh l xs)

data HereOrNot : (xs : Header k) -> (ys : Header k) -> Type where
  HN : {xs : OrdHeader k o} -> {ys : OrdHeader k o} ->
       HereOrNot xs ys -> HereOrNot (H xs) (H ys)

toSub : {xs : Header k} -> HereOrNot xs ys -> Maybe (Sub xs ys)
toSub (HN compat) = map S (toSub compat)


data Nub : (Header' label a) -> Type where
  N : {xs : OrdList k o a} -> Nub xs -> Nub (H xs)

IsNub : DecEq label => (xs : Header' label a) -> Type
IsNub (H xs) = IsYes (decNub xs)

namespace SubWithKeys

  data SubWithKeys : (List k) -> (xs : Header k) -> (ys : Header k) -> Type where
    S : {xs : OrdHeader k o } -> {ys : OrdHeader k o } ->
        SubWithKeys keys xs ys -> SubWithKeys keys (H xs) (H ys)

namespace SameOrd

  data SameOrd : (xs : Header k) -> (ys : Header k) -> Type where
    S : {xs : OrdHeader k o} -> {ys : OrdHeader k o} -> SameOrd xs ys -> SameOrd (H xs) (H ys)

namespace Decomp

  data Decomp : (required : Header k) -> (optional : Header k) -> (xs : Header k) -> Type where
    D : Header.Sub.Sub required xs -> HereOrNot optional xs -> Decomp required optional xs


diffKeys : DecEq k => (xs : Header k) -> (ys : Header k) -> Header k
diffKeys (H xs) (H ys) = H (diffKeys xs ys)

patch : DecEq k =>
        (xs : Header k) -> (ys : Header k) -> Header k
patch (H xs) (H ys) = H (patch xs ys)
