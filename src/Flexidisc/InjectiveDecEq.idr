||| This module provides a helper to implement a DecEq instance.
||| You only have to provide a InjectiveDecEq interfaces, and it will build
||| the DecEq instance on its own.
||| Most of the time, you will end up writing 2n statements instead of n^2.
module Flexidisc.InjectiveDecEq

%default total
%access public export

IsInjection : (a : Type) -> (f : a -> b) -> Type
IsInjection a f = (x,y : a) -> f x = f y -> x = y

decEqViaInjection : DecEq b =>
                    (toInj : a -> b) -> (isInj : IsInjection a toInj) ->
                    (x,y :a) -> Dec (x = y)
decEqViaInjection f isInj x y with (decEq (f x) (f y))
  | (Yes prf) = Yes (isInj x y prf)
  | (No contra) = No (contra . cong)

retrieveInjection : (func : a -> b) -> (cnuf : b -> a) ->
                    ((x : a) -> cnuf (func x) = x) ->
                    IsInjection a func
retrieveInjection func cnuf prf x y funcEq =
  rewrite sym (prf x) in
  rewrite sym (prf y) in cong funcEq

interface (DecEq a, DecEq b) => InjectiveDecEq a b | a where

  implementation DecEq a where
    decEq x y = let
      isInj = retrieveInjection inj ret inv
      in decEqViaInjection inj isInj x y

  inj : a -> b
  ret : b -> a
  inv : (x : a) -> ret (inj x) = x
