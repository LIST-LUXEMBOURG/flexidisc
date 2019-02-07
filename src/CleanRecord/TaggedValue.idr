module CleanRecord.TaggedValue

%default total

infixl 8 :=

public export
data TaggedValue : (key : k) -> (v : Type) -> Type where
  (:=) : (key : k) -> v -> TaggedValue key v
