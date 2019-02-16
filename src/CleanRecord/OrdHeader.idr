module CleanRecord.OrdHeader

import public CleanRecord.OrdList

%default total
%access public export

OrdHeader : (k : Type) -> (o : Ord k) -> Type
OrdHeader k o = OrdList k Type o

||| Update a value in the list given it's location and an update function
changeType : (xs : OrdHeader k o) -> (loc : OrdLabel l xs) -> (new : Type) ->
             OrdHeader k o
changeType = changeValue

optional : OrdHeader k o -> OrdHeader k o
optional [] = []
optional ((l, ty) :: xs) = (l, Maybe ty) :: optional xs

freshOnOptional : (p : Fresh l xs) -> Fresh l (optional xs)
freshOnOptional [] = []
freshOnOptional (f :: fresh) = f :: freshOnOptional fresh

optionalPreservesNub : {xs : OrdHeader k o} -> Nub xs -> Nub (optional xs)
optionalPreservesNub [] = []
optionalPreservesNub (p::prf) = freshOnOptional p :: optionalPreservesNub prf
