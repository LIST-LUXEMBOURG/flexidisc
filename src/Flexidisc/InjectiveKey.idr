||| This module provides a helper to implement a `DecEq`, `Eq`, and `Ord`
||| instances, which are required for a type that is used as a key in a `Record`.
||| You only have to provide a `InjectiveKey` interface, and it will build
||| the required instances on its own.
||| Most of the time, you will end up writing O(n) statements instead of O(n^2).
module Flexidisc.InjectiveKey

%default total
%access public export

||| Proof that `f` is an injection
IsInjection : (a : Type) -> (f : a -> b) -> Type
IsInjection a f = (x,y : a) -> f x = f y -> x = y

||| Decide equality via an injection
decEqViaInjection : DecEq b =>
                    (toInj : a -> b) -> (isInj : IsInjection a toInj) ->
                    (x,y : a) -> Dec (x = y)
decEqViaInjection f isInj x y with (decEq (f x) (f y))
  | (Yes prf) = Yes (isInj x y prf)
  | (No contra) = No (contra . cong)

||| Build an injection out of a function,
||| an inverse function for the target elements, and an
||| equality proof.
retrieveInjection : (func : a -> b) -> (cnuf : b -> a) ->
                    ((x : a) -> cnuf (func x) = x) ->
                    IsInjection a func
retrieveInjection func cnuf prf x y funcEq =
  rewrite sym (prf x) in
  rewrite sym (prf y) in cong funcEq

||| Comparaison thanks to an injection function
compareInj : Ord b => (a -> b) -> (x,y : a) -> Ordering
compareInj f x y = compare (f x) (f y)

||| Interface that provides a default implementation of typeclasses required to
||| be a record key.
interface (DecEq a, Eq a, Ord a,
           DecEq b, Eq b, Ord b) => InjectiveKey a b | a where

  implementation DecEq a where
    decEq x y = let
      isInj = retrieveInjection inj ret inv
      in decEqViaInjection inj isInj x y

  implementation Eq a where
    (==) x y = inj x == inj y

  implementation Ord a where
    compare x y = compareInj inj x y
    (<) x y = compareInj inj x y == LT
    (>) x y = compareInj inj x y == GT
    (<=) x y = compareInj inj x y /= GT
    (>=) x y = compareInj inj x y /= LT
    min x y = if compareInj inj x y == GT then y else x
    max x y = if compareInj inj x y == LT then y else x

  inj : a -> b
  ret : b -> a
  inv : (x : a) -> ret (inj x) = x
