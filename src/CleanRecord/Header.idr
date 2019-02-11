module CleanRecord.Header

import public CleanRecord.Dec.IsYes
import public CleanRecord.Header.Label
import public CleanRecord.Header.Row
import public CleanRecord.Header.Sub
import public CleanRecord.Header.Type

import CleanRecord.OrdHeader

%default total
%access public export

data CompWithKeys : (List k) -> (xs : Header k) -> (ys : Header k) -> Type where
  S : {xs : OrdHeader k o} -> {ys : OrdHeader k o} ->
      CompWithKeys keys xs ys -> CompWithKeys keys (H xs) (H ys)

data Disjoint : (xs : Header k) -> (ys : Header k) -> Type where
  D : {xs : OrdHeader k o} -> {ys : OrdHeader k o} ->
      Disjoint xs ys -> Disjoint (H xs) (H ys)


data Fresh : (l : label) -> (xs : Header label) -> Type where
  F : {xs : OrdHeader k o} -> Fresh l xs -> Fresh l (H xs)

%name Header.Fresh fresh, prf, new

IsFresh : (DecEq label) => (l : label) -> (xs : Header label) -> Type
IsFresh l (H xs) = IsYes (decFresh l xs)


data HereOrNot : (xs : Header k) -> (ys : Header k) -> Type where
  HN : {xs : OrdHeader k o1} -> {ys : OrdHeader k o2} ->
       HereOrNot xs ys -> HereOrNot (H xs) (H ys)


data Nub : (Header label) -> Type where
  N : {xs : OrdHeader k o} -> Nub xs -> Nub (H xs)

namespace SubWithKeys

  data SubWithKeys : (List k) -> (xs : Header k) -> (ys : Header k) -> Type where
    S : {xs : OrdHeader k o } -> {ys : OrdHeader k o } ->
        SubWithKeys keys xs ys -> SubWithKeys keys (H xs) (H ys)

namespace SmaeOrd

  data SameOrd : (xs : Header k) -> (ys : Header k) -> Type where
    S : {xs : OrdHeader k o} -> {ys : OrdHeader k o} -> SameOrd xs ys -> SameOrd (H xs) (H ys)

diffKeys : DecEq k => (xs : Header k) -> (ys : Header k) -> Header k
diffKeys (H xs) (H ys) = H (diffKeys xs ys)

patch : DecEq k =>
        (xs : Header k) -> (ys : Header k) -> Header k
patch (H xs) (H ys) = H (patch xs ys)
