module TypeOperators

%access public export
  
infixr 1 :->

(:->) : (a, b : i -> Type) -> (i -> Type)
(:->) a b i = a i -> b i

infixr 2 :+

(:+) : (a, b : i -> Type) -> (i -> Type)
(:+) a b i = Either (a i) (b i)
  
infixr 3 :*

(:*) : (a, b : i -> Type) -> (i -> Type)
(:*) a b i = (a i, b i)  

Cst : Type -> (i -> Type)
Cst t _ = t

All : (a : i -> Type) -> Type
All {i} a = {j : i} -> a j
