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

instance decidable_eq_self {α} (x : α) : decidable (x = x) := is_true rfl

example : ite (5 = 5) true false := trivial

example : ¬(ite (5 ≠ 5) true false) := false.elim 

def as_true (c : Prop) [decidable c] : Prop := ite c true false

def of_as_true {c : Prop} [h₁ : decidable c] (h₂ : as_true c) : c :=
match h₁, h₂ with
| (is_true hc),  h₂ := hc
| (is_false _),  h₂ := false.elim h₂
end

example : decidable (5 ≠ 5) := infer_instance

open mynat

instance decidable_mynat_le (a : mynat) : ∀ b : mynat, decidable (a ≤ b) :=
begin
  induction a with a ha,
  { intro b, apply is_true, apply mynat.zero_le, },
  { intro b,
    induction b with b hb,
    { apply is_false, apply not_succ_le_zero, },
    { cases ha b with h h,
      { apply is_false, intro h₂,
        apply h, exact le_of_succ_le_succ h₂, },
      { apply is_true, exact succ_le_succ_of_le h, }, } },
end

example : ite ((20 : mynat) ≤ 30) true false := trivial


example : ¬ ite ((30 : mynat) ≤ 20 ) true false := false.elim

example (x : mynat) : ite (((5 : mynat) ≤ 6) ∧ (x = x)) true false := trivial

example (x : mynat) : as_true (((5 : mynat) ≤ 6) ∧ (x = x))  := trivial

example : as_true ((50 : mynat) ≤ 60) := trivial

example : as_true ((0 : mynat) ≤ 5) = true := rfl

example : (20 : mynat) ≤ 30 ∧ (5 : mynat) = 5:= of_as_true trivial

example [h₁ : decidable (5 ≠ 5)] (h₂ : as_true (5 ≠ 5)) : 5 ≠ 5 := of_as_true h₂

instance decidable_eq_zero : ∀ (y : mynat) , decidable (zero = y)
| zero      := is_true rfl
| (succ _)  := is_false (succ_ne_zero _).symm


instance decidable_eq (x : mynat) : ∀ y : mynat, decidable (x = y) :=
begin
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

lemma fifteen_eq_five_plus_ten : (15 : mynat) = 5+10 := of_as_true (by trivial)

--set_option pp.all true

--#print fifteen_eq_five_plus_ten

example : (5 : mynat) ≠ 20 := of_as_true (by trivial)

end hidden

lemma foo : ite (5 = 6) 10 20 = 20 := rfl

lemma bar : ite (5 ≠ 6) 10 20 = 10 := rfl

lemma bar' : (if (5 ≠ 6) then 10 else 20) = 10 := rfl

example : decidable (5 = 6) := nat.decidable_eq 5 6

lemma decidable_not (p : Prop) [decidable p] : decidable ¬p :=
dite p (λ (h : p), decidable.is_false $ λ (hn : ¬p), hn h) (λ (h : ¬p) , decidable.is_true h)

lemma em' (p : Prop) [decidable p] : p ∨ ¬p := dite p (λ hp, or.inl hp) (λ hnp, or.inr hnp)

lemma em'' (p : Prop) [decidable p] : p ∨ ¬p := if hp : p then or.inl hp else or.inr hp

lemma boo (p : Prop) [decidable p] : p ∨ ¬p := if hp : p then or.inl hp else or.inr hp

def mod : ℕ → ℕ → ℕ
| a 0       := a
| a (b + 1)   :=  
if h : a < (b + 1) then a else
  have a - (b + 1) < a, from nat.sub_lt (show 0 < a, by linarith) (show 0 < (b+1), by linarith),
  mod (a - (b + 1)) (b + 1)

  example : (5 ≠ 7) ∧ (10 ≤ 20) := dec_trivial