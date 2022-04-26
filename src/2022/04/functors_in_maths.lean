import category_theory.types

universes u

variables {X : Type u} 

open category_theory

/-
We'll show that for any type `X`, the type `set X` of subsets of `X` is a category.

* `hom`: for each subset `S` and `T` of `X`, a term of type `hom S T` is a function of type
  `S → T`. We denote by `S ⟶ T` a term of type `hom S T`.
* `id`: For each `S : set X`, we give a term of type `S ⟶ S`. We'll take `id : S → S`.
* `comp`: compositions of `hom`s is composition of functions.
* `id_comp'`, `comp_id'`, `assoc`: these properties follow immediately from the same properties
for function composition. 
-/

def set_cat : category (set X) :=
{ hom       := λ S T, (S → T),
  id        := λ S, id,
  comp      := λ S T U f g, g ∘ f,
  id_comp'  := λ S T f, rfl,
  comp_id'  := λ S T f, rfl,
  assoc'    := λ S T U V f g h, rfl }

/-
In `category_theory.types`, it is shown that each Lean type is a large category, Type.
-/

def powerset_functor : Type u ⥤ Type u :=
{ obj       := λ X, set X,
  map       := λ X Y f S, f '' S,
  map_id'   := λ X, funext (λ S, by simp),
  map_comp' := λ X Y Z f g, funext (λ S, by {ext, simp}) }