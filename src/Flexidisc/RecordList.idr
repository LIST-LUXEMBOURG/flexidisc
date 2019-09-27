module Flexidisc.RecordList

import Flexidisc.Record
import Flexidisc.Record.Transformation

%default total
%access export

public export
data RecordListM : (m : Type -> Type) -> (label : Type) -> List (Header label) -> Type where
  Nil  : RecordListM m label []
  (::) : RecordM m label header -> RecordListM m label headers ->
         RecordListM m label (header :: headers)

%name RecordListM xss, yss, zss

public export
RecordList : (label : Type) -> List (Header label) -> Type
RecordList = RecordListM id

public export
recordList : RecordListM m label xss -> RecordListM m label xss
recordList = id

namespace ContentConstraint

  public export
  data All : (Header label -> Type) ->
             (List (Header label)) -> Type where
    Nil : All cst []
    (::) : cst xs -> All cst xss -> All cst (xs::xss)

  public export
  data One : (Header label -> Type) -> Header label ->
             (List (Header label)) -> Type where
    Here  : cst xs -> One cst xs (xs :: xss)
    There : One cst ys xss -> One cst ys (xs::xss)

toList : RecordListM m label xss -> {auto prf : All (Sub subset) xss} ->
         List (RecordM m label subset)
toList [] = []
toList (x :: xs) {prf = _ :: prf} = project x :: toList xs

get : (xss : RecordListM m label headers) -> One cst header headers ->
      RecordM m label header
get (xs :: _)  (Here prf) = xs
get (_ :: xss) (There later) = get xss later

firstWith : DecEq k => TransformationM Maybe k mapper -> RecordList k xss ->
            {auto prf : All (HereOrNot (toSource mapper)) xss} ->
            Maybe (header ** Record k header)
firstWith f [] = Nothing
firstWith f (xs :: xss) {prf = p::_} = checkOne <|> firstWith f xss
  where
    checkOne = do
      toSub p
      res <- patchRecord f xs
      pure (_ ** res)

foldAll : (Ord k, DecEq k) => RecordFunc req opt a -> RecordList k xss ->
          {auto optNub : IsNub opt} ->
          {auto prf : All (Decomp req opt) xss} -> List a
foldAll f [] = []
foldAll f (xs :: xss) {prf = p :: prf} = foldRecord f xs :: foldAll f xss
