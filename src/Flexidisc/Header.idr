module Flexidisc.Header

import public Flexidisc.Dec.IsYes
import public Flexidisc.Header.Label
import public Flexidisc.Header.Row
import public Flexidisc.Header.Sub
import public Flexidisc.Header.Type
import public Flexidisc.OrdList

%default total
%access public export

||| A proof that a header some keys added to an given header leads to another one
||| @skipped keys of the original header that are not in the subset
||| @subset part of thecoriginal header
||| @subset the original header
data CompWithKeys : (skipped : List k) ->
                    (subset, orig : Header' k a) ->
                     Type where
  ||| Wrap `OrdList.CompWithKeys`
  S : {xs : OrdList k o a} -> {ys : OrdList k o a} ->
      CompWithKeys keys xs ys -> CompWithKeys keys (H xs) (H ys)

||| A proof that two `Header'` don't share a key.
data Disjoint : (xs, ys : Header' k a) -> Type where
  D : {xs : OrdList k o a} -> {ys : OrdList k o a} ->
      Disjoint xs ys -> Disjoint (H xs) (H ys)


||| A proof that a label is not already in a `Header'`
data Fresh : (l : label) -> (xs : Header' label a) -> Type where
  F : {xs : OrdList k o a} -> Fresh l xs -> Fresh l (H xs)

%name Header.Fresh fresh, prf, new

||| Decision procedure for freshness
decFresh : (DecEq label) => (l : label) -> (xs : Header' label a) ->
           Dec (Fresh l xs)
decFresh l (H xs) with (decFresh l xs)
  | (Yes prf) = Yes (F prf)
  | (No contra) = No (\(F x) => contra x)

||| Move the `decFresh` procedure to the type level
IsFresh : (DecEq label) => (l : label) -> (xs : Header' label a) -> Type
IsFresh l xs = IsYes (decFresh l xs)

||| A proof that labels that are in both lists have the same values
data HereOrNot : (xs, ys : Header' k a) -> Type where
  HN : {xs, ys : OrdList k o a} ->
       HereOrNot xs ys -> HereOrNot (H xs) (H ys)

toSub : {xs : Header k} -> HereOrNot xs ys -> Maybe (Sub xs ys)
toSub (HN compat) = map S (toSub compat)


||| A proof that a Header' has no duplicated key
data Nub : (Header' label a) -> Type where
  N : {xs : OrdList k o a} -> Nub xs -> Nub (H xs)

IsNub : DecEq label => (xs : Header' label a) -> Type
IsNub (H xs) = IsYes (decNub xs)

namespace SubWithKeys

  ||| Proof that an `Header'` has some given `keys` and is a subset of an other
  data SubWithKeys : (List k) -> (xs, ys : Header' k a) -> Type where
    S : {xs, ys : OrdList k o a} ->
        SubWithKeys keys xs ys -> SubWithKeys keys (H xs) (H ys)

namespace SameOrd

  ||| Both Header' are ordered with the same Ord typeclass
  ||| (thank you non unique typeclasses)
  data SameOrd : (xs, ys : Header' k a) -> Type where
    S : {xs, ys : OrdList k o a} -> SameOrd xs ys -> SameOrd (H xs) (H ys)

namespace Decomp

  ||| A Decomposition of a Header' into
  ||| a set of required values and a set of optional values
  ||| @required the set keys and types that must be in the original header
  ||| @optional the set keys and types that can be in the original header
  ||| @xs the original header
  data Decomp : (required, optional : Header k) -> (xs : Header k) -> Type where
    D : Header.Sub.Sub required xs -> HereOrNot optional xs -> Decomp required optional xs

||| Output the keys of the first Header' that are not in the second Header'
diffKeys : DecEq k => (xs, ys : Header' k a) -> Header' k a
diffKeys (H xs) (H ys) = H (diffKeys xs ys)

||| Apply a patch `xs` to an `Header'` `ys`.
||| The label of `ys` that are in `xs` are updated,
||| and the fresh element of `xs` are added
patch : DecEq k => (xs, ys : Header' k a) -> Header' k a
patch (H xs) (H ys) = H (patch xs ys)
