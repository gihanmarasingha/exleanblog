import tactic

namespace exlean 

open nat

@[elab_as_eliminator]
lemma nat_ind (P : ℕ → Prop) (n : ℕ)  (h₀ : P 0) (h₁ : ∀ (k : ℕ), P k → P k.succ) : P n :=
nat.rec_on n h₀ h₁

lemma add_zero (a : ℕ) : a + 0 = a := rfl

lemma add_succ (a b : ℕ) : a + succ b = succ (a + b) := rfl

def P := λ k, 0 + k = k

example : (P 0) = (0 = 0 + 0) := rfl

lemma base : P 0 := add_zero 0

lemma ind_step : ∀ k, P k → P k.succ :=
begin
  unfold P,
  intros k ih, -- k : ℕ, ih : 0 + k = k, ⊢ 0 + (succ k) = succ k
  rw add_succ, -- ⊢ succ (0 + k) = succ k
  rw ih, -- ⊢ succ k = succ k
end

lemma zero_add (a : ℕ) : 0 + a = a := nat_ind P a base ind_step

lemma zero_add' (a : ℕ) : 0 + a = a :=
begin
  let P := λ k, 0 + k = k,
  have h₀ : P 0, { dsimp [P], refl, },
  have h₁ : ∀ (k : ℕ), P k → P k.succ,
  { dsimp [P], intros k ih, rw add_succ, rw ih, },
  exact nat_ind P a h₀ h₁
end

lemma zero_add'' (a : ℕ) : 0 + a = a :=
begin
  apply nat_ind (λ k, 0 + k = k),
  { refl, },
  { intros k ih, rw [add_succ, ih], },
end

lemma zero_add''' : ∀ a : ℕ, 0 + a = a := @nat.rec (λ k, 0 + k = k) rfl (λ k ih, 
  have h₂ : 0 + succ k = succ (0 + k) := add_succ 0 k,
  have h₃ : succ (0 + k) = succ k := ih.symm ▸ rfl,
  eq.trans h₂ h₃)

lemma zero_add'''' (a : ℕ) : 0 + a = a := nat_ind _ a rfl
(λ k ih, eq.trans (add_succ 0 k) (ih.symm ▸ rfl))

lemma zero_add''''' (a : ℕ) : 0 + a = a := nat.rec_on a rfl (λ k ih, 
  have h₂ : 0 + succ k = succ (0 + k) := add_succ 0 k,
  have h₃ : succ (0 + k) = succ k := ih.symm ▸ rfl,
  eq.trans h₂ h₃)

universe u

@[elab_as_eliminator]
lemma nat_rec_on {C : ℕ → Sort u} (n : ℕ) (h₀ : C 0) (h₁ : ∀ (k : ℕ), C k → C k.succ) : C n :=
nat.rec_on n h₀ h₁

abbreviation C := λ (k : ℕ), ℕ

example : ∀ (k : ℕ), (C k) = (C (succ k)) := λ k, rfl

-- The following sequence is `a₀ = 6` and `aₙ₊₁ = 5 + 2 * aₙ`.
def myseq' (n : ℕ) : ℕ := @nat.rec_on (λ k, ℕ) n 6 (λ k seq_k, 5 + 2 * (seq_k))

-- Here's another way to write the sequence.
def myseq (n : ℕ) : ℕ := nat.rec_on n 6 (λ k seq_k, 3 + 2 * (succ seq_k))

lemma myseq_succ (n : ℕ) : myseq (succ n) = 3 + 2 * (succ (myseq n)) := rfl

lemma myseq_formula' (n : ℕ) : 5 + myseq n = 11 * 2 ^ n:=
begin
  induction n with n ih,
  { refl, },
  { have h : ∀ a, 5 + (3 + 2 * (succ a)) = 2 * (5 + a), { intro a, ring, },
    simp only [myseq_succ, h, ih], ring_exp, },
end

lemma myseq_formula (n : ℕ) : myseq n = 11 * 2 ^ n - 5 :=
begin
  symmetry,
  apply nat.sub_eq_of_eq_add,
  rw ←myseq_formula',
end

def myseq2 (n : ℕ) : ℕ := nat.rec_on n 0 (λ k seq_k, k + succ seq_k)

lemma myseq3 (n : ℕ) : vector ℕ n := nat.rec_on n vector.nil (λ k seq_k, vector.cons (k*k) seq_k)

def add_one (n : ℕ) : ℕ := nat.rec_on n 1 (λ k ih, succ ih)

def add_one' (n : ℕ) : ℕ := @nat.rec_on (λ x, ℕ) n 1 (λ k ih, succ ih)

def add_two (n : ℕ) : ℕ := nat.rec_on n 2 (λ k ih, succ ih)

example : add_one 4 = 5 := rfl

example : add_two 4 = 6 := rfl

def myadd (m n : ℕ) : ℕ := nat.rec_on n m (λ k ih, succ ih)

example : myadd 11 5 = 16 := rfl

example : ∀ n, add_two n = myadd 2 n := λ n, rfl

inductive le (a : ℕ) : ℕ → Prop
| refl : le a
| step : ∀ {b}, le b → le (succ b)

local infix ` ≤ ` := le

lemma le_rec (x : ℕ) (C : ℕ → Prop) (h1 : C x) (h2 : (∀ (y : ℕ), x ≤ y → C y → C y.succ)) :
 ∀ {n : ℕ}, x ≤ n → C n := λ n, (le.rec h1) h2

lemma le_rec' (x n : ℕ) (C : ℕ → Prop)
(h1 : C x) (h2 : (∀ (y : ℕ), x ≤ y → C y → C y.succ)) (h3 : x ≤ n) : C n :=
 (λ n, (le.rec h1) h2) n h3

lemma le_trans (a b c : ℕ) : a ≤ b → b ≤ c → a ≤ c :=
begin
  let C := λ m, a ≤ m,
  intro hab,
  have h2 : ∀ (y : ℕ), b ≤ y → C y → C y.succ,
  { intros y hby hay,
    apply le.step,
    exact hay, },
  apply le_rec b C hab h2,
end

lemma le_trans' (a b c : ℕ) : a ≤ b → b ≤ c → a ≤ c :=
begin
  let C := λ m, a ≤ m,
  intros h1 h3,
  have h2 : ∀ (y : ℕ), b ≤ y → C y → C y.succ,
  { intros y hby hay,
    apply le.step,
    exact hay, },
  exact le_rec' b c C h1 h2 h3,
end



end exlean