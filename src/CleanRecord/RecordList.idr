module CleanRecord.RecordList

import CleanRecord.Record
import CleanRecord.Record.Transformation

%default total
%access export

public export
data RecordList : (label : Type) -> List (Header label) -> Type where
  Nil  : RecordList label []
  (::) : Record label header -> RecordList label headers ->
         RecordList label (header :: headers)

%name RecordList xss, yss, zss

public export
recordList : RecordList label xss -> RecordList label xss
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

toList : RecordList label xss -> {auto prf : All (Sub subset) xss} ->
         List (Record label subset)
toList [] = []
toList (x :: xs) {prf = _ :: prf} = project x :: toList xs

get : (xss : RecordList label headers) -> One cst header headers ->
      Record label header
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
      res <- patchM f xs
      pure (_ ** res)

foldAll : (Ord k, DecEq k) => RecordFunc req opt a -> RecordList k xss ->
          {auto optNub : IsNub opt} ->
          {auto prf : All (Decomp req opt) xss} -> List a
foldAll f [] = []
foldAll f (xs :: xss) {prf = p :: prf} = foldRecord f xs :: foldAll f xss
