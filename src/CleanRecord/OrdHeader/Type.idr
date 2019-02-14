module CleanRecord.OrdHeader.Type

import public CleanRecord.OrdList.Fresh
import public CleanRecord.OrdList.Label
import public CleanRecord.OrdList.Type
import public CleanRecord.OrdList.Nub

%default total
-- Should hide more from it to ensure that we do not mess up with forge header
%access public export

OrdHeader : (k : Type) -> (o : Ord k) -> Type
OrdHeader k o = OrdList k Type o

optional : OrdHeader k o -> OrdHeader k o
optional [] = []
optional ((l, ty) :: xs) = (l, Maybe ty) :: optional xs

freshOnOptional : (p : Fresh l xs) -> Fresh l (optional xs)
freshOnOptional [] = []
freshOnOptional (f :: fresh) = f :: freshOnOptional fresh

optionalPreservesNub : {xs : OrdHeader k o} -> Nub xs -> Nub (optional xs)
optionalPreservesNub [] = []
optionalPreservesNub (p::prf) = freshOnOptional p :: optionalPreservesNub prf
