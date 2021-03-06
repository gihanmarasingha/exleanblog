import tactic

/-!
# Haskell Functors

In the Haskell programming language, the class `Functor` is 

-/

#check int

universes u

variables (α β : Type u)

class Functor (f : Type u → Type u) :=
(fmap : (α → β) → f α → f β)

instance listFunctor : Functor α β list := ⟨list.map⟩

#check list

def boo : functor list :=
{ map := λ α β, list.map,
  map_const := λ α β x ys, [x] }



