module Success

import Data.Vect
import TypeOperators

%access public export

record Success (a : Type) (n : Nat) where
  constructor MkSuccess
  Value : a
  {Size : Nat}
  Small : LT Size n
  Leftovers : Vect Size Char

map : (f : a -> b) -> All (Success a :-> Success b)
map f (MkSuccess v s lfts) = MkSuccess (f v) s lfts
