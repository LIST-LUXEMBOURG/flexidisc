module CleanRecord.RecordList

import CleanRecord

%default total
%access export

public export
data RecordList : List (List (Field label)) -> Type where
  Nil  : RecordList []
  (::) : Record header -> RecordList headers -> RecordList (header :: headers)

public export
recordList : RecordList xss -> RecordList xss
recordList = id

namespace ContentConstraint

  public export
  data All : (List (Field label) -> Type) ->
             (List (List (Field label))) -> Type where
    Nil : All cst []
    (::) : cst xs -> All cst xss -> All cst (xs::xss)

  public export
  data One : (List (Field label) -> Type) -> List (Field label) ->
             (List (List (Field label))) -> Type where
    Here  : cst xs -> One cst xs (xs :: xss)
    There : One cst ys xss -> One cst ys (xs::xss)

toList : RecordList xss -> {auto prf : All (Sub subset) xss} ->
         List (Record subset)
toList [] = []
toList (x :: xs) {prf = _ :: prf} = project x :: toList xs

get : (xss : RecordList headers) -> One cst header headers -> Record header
get (xs :: _)  (Here prf) = xs
get (_ :: xss) (There later) = get xss later

private
checkKeys : DecEq label =>
              {xs : List (Field label)} ->
              List label -> Record xs -> Maybe (Record xs)
checkKeys [] x = pure x
checkKeys (y :: xs) x with (decLabel y x)
  | (Yes prf) = checkKeys xs x
  | (No contra) = Nothing

filterByKeys : DecEq label =>
               {xss : List (List (Field label))} ->
               List label -> RecordList xss ->
               (yss : List (List (Field label)) ** RecordList yss)
filterByKeys xs [] = ([] ** [])
filterByKeys xs (y :: ys) with (filterByKeys xs ys)
  | (yss ** res) = maybe (yss ** res)
                         (\r => (_::yss ** r::res))
                         (checkKeys xs y)

private
getSub : DecEq label =>
         {header : List (Field label)} ->
         Record header -> Compliance header q -> IsNub q -> Maybe (Record q)
getSub _ Empty _ = Just (rec [])
getSub _ (Skip _ _) _ = Nothing
getSub xs (Keep loc prf) (p::nubPrf) = let
  value = atRow xs loc
  in map (\ys => cons value ys) (getSub xs prf nubPrf)

private
checkMatch : (DecEq label, Eqs q) => {header : List (Field label)} ->
                      (query : Record q) ->
                      (ys : Record header) ->
                      (prf : (\xs => Compliance xs q) header) ->
                      Maybe (res : List (Field label) ** Record res)
checkMatch query@(MkRecord xs nubProof) ys prf =
  getSub ys prf nubProof >>= (\xs => if query == xs then Just (_ ** ys)
                                                    else Nothing)

matchOne : (DecEq label, Eqs q) =>
           {headers : List (List (Field label))} ->
           (query : Record q) -> (xss : RecordList headers) ->
           {auto prf : All (\xs => Compliance xs q) headers} ->
           Maybe (xs : List (Field label) ** Record xs)
matchOne query [] = Nothing
matchOne query (ys :: yss) {prf = p :: prf} =
  checkMatch query ys p <|> matchOne query yss

private
checkMissingKeys : DecEq label =>
                   {xs : List (Field label)} ->
                   List label -> Record xs -> Maybe (Record xs)
checkMissingKeys [] x = pure x
checkMissingKeys (y :: xs) x with (decLabel y x)
  | (Yes prf) = Nothing
  | (No contra) = checkMissingKeys xs x

filterByMissingKeys : DecEq label =>
                      {xss : List (List (Field label))} ->
                      List label -> RecordList xss ->
                      (yss : List (List (Field label)) ** RecordList yss)
filterByMissingKeys xs [] = ([] ** [])
filterByMissingKeys xs (y :: ys) with (filterByMissingKeys xs ys)
  | (yss ** res) = maybe (yss ** res)
                         (\r => (_::yss ** r::res))
                         (checkMissingKeys xs y)
