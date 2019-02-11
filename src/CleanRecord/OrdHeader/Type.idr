module CleanRecord.OrdHeader.Type

import public CleanRecord.OrdList.Type

%default total
-- Should hide more from it to ensure that we do not mess up with forge header
%access public export

OrdHeader : (k : Type) -> (o : Ord k) -> Type
OrdHeader k o = OrdList k Type o
