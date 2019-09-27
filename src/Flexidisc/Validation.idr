module Flexidisc.Validation

%default total
%access public export

data Validation e a = Error e | Valid a

implementation Functor (Validation e) where
  map func (Error x) = Error x
  map func (Valid x) = Valid (func x)

implementation Semigroup e => Applicative (Validation e) where
  pure x = Valid x
  (<*>) (Error x) (Error y) = Error (x <+> y)
  (<*>) (Error x) (Valid _) = Error x
  (<*>) (Valid _) (Error y) = Error y
  (<*>) (Valid f) (Valid x) = Valid (f x)

implementation (Show e, Show a) => Show (Validation e a) where
  show (Error x) = "❌ " <+> show x
  show (Valid x) = "✅ " <+> show x:

export
validate : (a -> e) -> (a -> Bool) -> a -> Validation e a
validate err f x = if f x then Valid x else Error (err x)

export
validateL : (Applicative f, Semigroup (f e)) => (a -> e) -> (a -> Bool) -> a -> Validation (f e) a
validateL err f x = if f x then Valid x else Error (pure (err x))
