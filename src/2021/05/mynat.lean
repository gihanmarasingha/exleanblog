import tactic

inductive mynat : Type
| zero      : mynat
| succ      : mynat → mynat

open mynat

def mynat_to_nat : mynat → nat
| zero      := 0
| (succ n)  := nat.succ $ mynat_to_nat n

def nat_to_mynat : nat → mynat
| nat.zero      := zero
| (nat.succ n)  := succ $ nat_to_mynat n

def mynat_to_str : mynat → string := to_string ∘ mynat_to_nat

instance : has_repr mynat := ⟨mynat_to_str⟩

instance : has_zero mynat := ⟨zero⟩

instance : has_coe mynat nat := ⟨mynat_to_nat⟩

instance : has_coe nat mynat := ⟨nat_to_mynat⟩

namespace mynat

def pred : mynat → mynat
| zero      := zero
| (succ a)  := a

def add : mynat → mynat → mynat
| n   zero   := n
| n (succ m) := succ (add n m)

instance : has_one mynat := ⟨zero.succ⟩ 

instance : has_add mynat := ⟨add⟩

inductive le (a : mynat) : mynat → Prop
| refl : le a
| step : ∀ {b}, le b → le (succ b)

def lt (a b : mynat) := le (succ a) b

instance : has_le mynat := ⟨le⟩

instance : has_lt mynat := ⟨lt⟩

@[refl] lemma refl (a : mynat) : a ≤ a := le.refl

lemma le_succ_of_le {a b : mynat} (h : a ≤ b) : a ≤ b.succ := le.step h

lemma zero_le (a : mynat) : zero ≤ a :=
begin
  induction a with a ih,
  { refl, },
  { apply le.step, exact ih, }
end

lemma le_of_succ_le {a b : mynat} (h : a.succ ≤ b) : a ≤ b :=
begin
  induction h,
  case refl { apply le_succ_of_le, refl, },
  case step : _ _ h₃ { exact le_succ_of_le h₃, },
end

lemma succ_le_succ_of_le {a b : mynat} (h : a ≤ b) : a.succ ≤ b.succ :=
begin
  induction h,
  case refl { refl, },
  case step : _ _ h₃ { exact le_succ_of_le h₃, }
end

lemma pred_le_pred {a b : mynat} (h : a ≤ b) : pred a ≤ pred b :=
begin
  induction h,
  case refl { refl, },
  case step : _ h₂ _ { 
    induction a with a ih,
    { exact zero_le _, },
    { exact le_of_succ_le h₂, }, }
end

lemma le_of_succ_le_succ {a b : mynat} (h : a.succ ≤ b.succ) : a ≤ b := pred_le_pred h

lemma succ_ne_zero (n : mynat) : n.succ ≠ zero
.

lemma succ_ne_self (a : mynat) : a.succ ≠ a :=
begin
  induction a,
  case zero { exact succ_ne_zero _, },
  case succ : a ih { intro h₂, apply ih, exact mynat.no_confusion h₂ id },
end

lemma not_succ_le_zero : ∀ (n : mynat), succ n ≤ zero → false
.

lemma not_succ_le_self (a : mynat) : ¬(succ a ≤ a) :=
begin
  intro h,
  induction a with b ih,
  { exact not_succ_le_zero _ h, },
  { apply ih, exact le_of_succ_le_succ h, }
end

/-
Extra results
-/
lemma zero_lt_of_ne_zero (a : mynat) (h : a ≠ zero) : zero < a :=
begin
  induction a with a ih,
  { contradiction, },
  { by_cases h₂ : a = zero,
    { rw h₂, change zero.succ ≤ zero.succ, refl, },
    { apply le.step, apply ih, exact h₂, }, }, 
end

lemma succ_pos (a : mynat) : zero < a.succ := zero_lt_of_ne_zero _ (succ_ne_zero _)

@[trans] lemma le_trans {a b c : mynat} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := 
begin
  induction h₂,
  case refl { exact h₁ },
  case step : _ _ h { exact le.step h }
end

end mynat