import algebra.group group_theory.subgroup

-- `G` and `H` are groups
variables {G H : Type} [group G] [group H]

open subgroup

-- `A` and `B` are normal subgroups of `G` and `H` respectively.
variables {A : subgroup G} [normal A] {B : subgroup H} [normal B]

-- The following is, essentially, the definition of normal subgroup.
--lemma normal_def : ∀ n ∈ A, ∀ g : G, g * n * g⁻¹ ∈ A:= normal.conj_mem infer_instance

lemma normal_def {K : subgroup G} : normal K ↔ ∀ n ∈ K, ∀ g : G, g * n * g⁻¹ ∈ K :=
⟨λ h, h.conj_mem, λ h, ⟨h⟩⟩ 

lemma conj_mem_of_normal {K : subgroup G} [normal K] : ∀ n ∈ K, ∀ g : G, g * n * g⁻¹ ∈ K
  := normal_def.mp infer_instance


-- We now prove that `A × B` is a normal subgroup of `G × H`
-- Note that the (subgroup) product is written `prod A B` rather than `A × B`.

lemma normal_prod : normal (prod A B) :=
{ conj_mem := begin
  rintros ⟨a, b⟩ hin ⟨g, h⟩,
  rw prod.inv_mk, -- The result that `(s, t)⁻¹ = (t⁻¹, s⁻¹)`
  rw prod.mk_mul_mk, -- The result that `(p, q) * (s, t) = (p * s, q * t)`
  rw prod.mk_mul_mk,
  rw mem_prod at hin ⊢, -- The result that `(u, v) ∈ prod U V ↔ u ∈ U ∧ v ∈ V`.
  dsimp at hin ⊢, -- Make things look nicer.
  rcases hin with ⟨ha, hb⟩,
  split,
  { apply conj_mem_of_normal, apply ha, },
  { apply conj_mem_of_normal, apply hb },
end
}