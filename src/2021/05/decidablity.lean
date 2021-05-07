import tactic .mynat

namespace hidden

class inductive decidable (p : Prop) : Type
| is_false  : ¬p → decidable
| is_true   : p → decidable

open hidden.decidable

instance decidable_true : decidable true := is_true trivial

instance decidable_false : decidable false := is_false (λ q, false.elim q)

instance decidable_not (p : Prop) [h : decidable p] : decidable ¬p :=
match h with
| (is_false hnp)  := is_true hnp
| (is_true hp)    := is_false (λ hnp, hnp hp)
end

instance decidable_and (p q : Prop) [h₁ : decidable p] [h₂ : decidable q] : decidable (p ∧ q) :=
match h₁, h₂ with
| (is_false hnp), h₂              := is_false (λ hpq, hnp hpq.left)
| (is_true hp),   (is_false hnq)  := is_false (λ hpq, hnq hpq.right)
| (is_true hp),   (is_true hq)    := is_true ⟨hp, hq⟩ 
end

lemma decidable_and' (p q : Prop) [h₁ : decidable p] [h₂ : decidable q] : decidable (p ∧ q) :=
begin
  tactic.unfreeze_local_instances,
  cases h₁ with hnp hp,
  { apply is_false, intro hpq, exact hnp hpq.1, },
  { cases h₂ with hnq hq,
    { apply is_false, intro hpq, exact hnq hpq.2, },
    { exact is_true ⟨hp, hq⟩ } },
end

def decidable_or' (p q : Prop) [h₁ : decidable p] [h₂ : decidable q] : decidable (p ∨ q) :=
begin
  rw [←@not_not (p ∨ q), not_or_distrib],
  apply_instance, 
end

instance decidable_or (p q : Prop) [h₁ : decidable p] [h₂ : decidable q] : decidable (p ∨ q) :=
match h₁, h₂ with
| (is_true hp), h₂                := is_true (or.inl hp)
| (is_false hnp), (is_true hq)    := is_true (or.inr hq)
| (is_false hnp), (is_false hnq)  := is_false (λ hpq, or.elim hpq hnp hnq)
end

-- Note that `imp_iff_not_or` depends on the decidability of `p`.
instance decidable_if (p q : Prop) [h₁ : decidable p] [h₂ : decidable q] : decidable (p → q) :=
by { rw imp_iff_not_or, apply_instance }


instance decidable_iff (p q : Prop) [h₁ : decidable p] [h₂ : decidable q] : decidable (p ↔ q) :=
by { rw iff_def, apply_instance }

example (p q : Prop) [decidable p] [decidable q] : decidable $ (p ∧ q) → q := infer_instance

def ite (c : Prop) [d : decidable c] {α} (t e : α) : α := decidable.rec_on d (λ hnc, e) (λ hc, t)

def as_true (c : Prop) [decidable c] : Prop := ite c true false

def of_as_true {c : Prop} [h₁ : decidable c] (h₂ : as_true c) : c :=
match h₁, h₂ with
| (is_true hc),  h₂ := hc
| (is_false _),  h₂ := false.elim h₂
end

instance decidable_eq_self {α} (x : α) : decidable (x = x) := is_true rfl

open mynat

example (a : nat) : 0 < a.succ := nat.succ_pos a

example (a : nat) : ¬(nat.succ a ≤ a) := nat.not_succ_le_self a

instance decidable_mynat_le : ∀ a b : mynat, decidable (a ≤ b) :=
begin
  intro a,
  induction a with a ha,
  { intro b, apply is_true, apply mynat.zero_le, },
  { intro b,
    induction b with b hb,
    { apply is_false, apply not_succ_le_zero, },
    { cases ha b with h h,
      { apply is_false, intro h₂, apply h, exact le_of_succ_le_succ h₂, },
      { apply is_true, exact succ_le_succ_of_le h, }, } },
end

example : as_true ((20 : mynat) ≤ 30) := trivial

example : as_true ((0 : mynat) ≤ 5) = true := rfl

instance decidable_eq_zero : ∀ (y : mynat) , decidable (zero = y)
| zero      := is_true rfl
| (succ _)  := is_false (succ_ne_zero _).symm


instance decidable_eq: ∀ x y : mynat, decidable (x = y) :=
begin
  intro x,
  induction x,
  case zero { apply_instance, },
  case succ : x h
  { intro y, 
    induction y,
    case zero { apply is_false, apply succ_ne_zero, },
    case succ : z h₂
    { cases h₂,
      { cases (h z),
        case is_false : h₃ { apply is_false, intro h₄, apply h₃, exact succ.inj h₄, },
        case is_true : h₃ { apply is_true, rwa h₃, }, },
      { apply is_false, intro h₃, rw succ.inj_eq at h₃, rw h₃ at h₂, exact mynat.succ_ne_self _ h₂, }, } }
end

example : (15 : mynat) = 5+10 := of_as_true (by trivial)

example : (5 : mynat) ≠ 20 := of_as_true (by trivial)

instance decidable_iff_self (p : Prop) : decidable (p ↔ p) := is_true iff.rfl

example (p q : Prop) : as_true (p ∧ q ↔ p ∧ q) := trivial

end hidden
