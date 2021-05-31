import tactic data.vector

namespace exlean 

open nat

section induction_on_nat

@[elab_as_eliminator]
def nat.ind (P : ℕ → Prop) (n : ℕ)  (h₀ : P 0) (h₁ : ∀ (k : ℕ), P k → P k.succ) : P n :=
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

lemma zero_add (a : ℕ) : 0 + a = a := nat.ind P a base ind_step

lemma zero_add' (a : ℕ) : 0 + a = a :=
begin
  let P := λ k, 0 + k = k,
  have h₀ : P 0, { dsimp [P], refl, },
  have h₁ : ∀ (k : ℕ), P k → P k.succ,
  { dsimp [P], intros k ih, rw add_succ, rw ih, },
  exact nat.ind P a h₀ h₁
end

lemma zero_add'' (a : ℕ) : 0 + a = a :=
begin
  apply nat.ind (λ k, 0 + k = k),
  { refl, },
  { intros k ih, rw [add_succ, ih], },
end

lemma zero_add_apply_placeholder (a : ℕ) : 0 + a = a :=
begin
  apply nat.ind _ a,
  { refl, },
  { intros k ih, rw [add_succ, ih], },
end

lemma zero_add_refine (a : ℕ) : 0 + a = a :=
begin
  refine nat.ind _ a rfl _,
  { intros k ih, rw [add_succ, ih], },
end

lemma zero_add''' : ∀ a : ℕ, 0 + a = a := @nat.rec (λ k, 0 + k = k) rfl (λ k ih, 
  have h₂ : 0 + succ k = succ (0 + k) := add_succ 0 k,
  have h₃ : succ (0 + k) = succ k := ih.symm ▸ rfl,
  eq.trans h₂ h₃)

lemma zero_add'''' (a : ℕ) : 0 + a = a := nat.ind _ a rfl
(λ k ih, eq.trans (add_succ 0 k) (ih.symm ▸ rfl))

lemma zero_add''''' (a : ℕ) : 0 + a = a := nat.rec_on a rfl (λ k ih, 
  have h₂ : 0 + succ k = succ (0 + k) := add_succ 0 k,
  have h₃ : succ (0 + k) = succ k := ih.symm ▸ rfl,
  eq.trans h₂ h₃)

end induction_on_nat

section recursively_defined_sequences_of_ints

-- Here is recursion principle for defining sequences of integers.
/- def nat.int_seq (n : ℕ) (h₀ : ℤ) (h₁ : ∀ (k : ℕ), ℤ → ℤ) : ℤ :=
nat.rec_on n h₀ h₁ -/

def nat.int_seq (n : ℕ) (a₀ : ℤ) (h : ∀ (k : ℕ) (ak : ℤ), ℤ) : ℤ :=
nat.rec_on n a₀ h

-- The following is a sequence of integers with `a₀ = 6` and `aₙ₊₁ = 5 + 2 * aₙ`.
def seq1 (n : ℕ) : ℤ := nat.int_seq n (6 : ℤ) (λ k ak, 5 + 2 * ak)

lemma seq1_succ (k : ℕ) : seq1 (succ k) = 5 + 2 * (seq1 k) := rfl

example : seq1 2 = 39 := dec_trivial

-- We can easily prove a formula for the n-th term of the sequence.

-- First using the `induction` tactic
lemma seq1_formula (n : ℕ) : seq1 n = 11 * 2 ^ n - 5 :=
begin
  induction n with k ih,
  { refl, },
  { rw [seq1_succ, ih], ring_exp, }
end

-- Second, using `apply nat.ind`.
lemma seq1_formula' (n : ℕ) : seq1 n = 11 * 2 ^ n - 5 :=
begin
  apply nat.ind (λ n, seq1 n = 11 * 2 ^ n - 5),
  { refl, },
  { intros k ih, rw [seq1_succ, ih], ring_exp, },
end

lemma seq1_formula''' (n : ℕ) : seq1 n = 11 * 2 ^ n - 5 :=
begin
  refine nat.ind _ n rfl _,
  { intros k ih, rw [seq1_succ, ih], ring_exp, },
end

-- Third, using `nat.ind` term-style.
lemma seq1_formula'' (n : ℕ) : seq1 n = 11 * 2 ^ n - 5 :=
nat.ind _ n rfl (λ k ih, by {rw [seq1_succ, ih], ring_exp })

-- Here's another sequence.
def triangle (n : ℕ) : ℤ := nat.int_seq n 0 (λ k ak, k + ak)

lemma triangle_succ (n : ℕ) : triangle (succ n) = n + triangle n := rfl

-- We prove the formula for the sum of the triangle numbers.
lemma triangle_formula (n : ℕ) : 2 * triangle (succ n) = n * (succ n) :=
begin
  refine nat.ind _ n rfl _,
  { intros k ih, rw [triangle_succ, mul_add, ih], ring, }
end

lemma triangle_formula' (n : ℕ) : 2 * triangle (succ n) = n * (succ n) :=
nat.ind _ n rfl (λ k ih, by { rw [triangle_succ, mul_add, ih], ring })

end recursively_defined_sequences_of_ints

section recursively_defined_sequences_of_nats

-- Here's a principle for defining sequences of natural numbers.
def nat.nat_seq (n : ℕ) (h₀ : ℕ) (h₁ : ∀ (k : ℕ), ℕ → ℕ) : ℕ :=
nat.rec_on n h₀ h₁

-- The following sequence is `a₀ = 6` and `aₙ₊₁ = 5 + 2 * aₙ`.
def seq2 (n : ℕ) : ℕ := nat.nat_seq n 6 (λ k seq_k, 5 + 2 * seq_k)

lemma seq2_succ (n : ℕ) : seq2 (succ n) = 5 + 2 * (seq2 n) := rfl

-- Proving a formula is tricker in the ℕ case than in the ℤ case.
-- One approach is to use an auxiliary result.
lemma seq2_formula' (n : ℕ) : 5 + seq2 n = 11 * 2 ^ n :=
begin
  induction n with n ih,
  { refl, },
  { have h : ∀ a, 5 + (5 + 2 * a) = 2 * (5 + a), { intro a, ring },
    simp only [seq2_succ, h, ih], ring_exp, }
end

lemma seq2_formula (n : ℕ) : seq2 n = 11 * 2 ^ n - 5 :=
begin
  symmetry,
  apply nat.sub_eq_of_eq_add,
  rw ←seq2_formula',
end

end recursively_defined_sequences_of_nats

section sequences_of_vectors

def nat.vec_seq_simple (n : ℕ) (h : ∀ (k : ℕ) (ak : vector ℕ k), vector ℕ (k+1)) : vector ℕ n :=
  nat.rec_on n vector.nil h

def vseq (n : ℕ) : vector ℕ n := nat.vec_seq_simple n (λ k ak, vector.cons (k*k) ak)

def nat.vec_seq (n : ℕ) (a₀ : ℕ) (h : ∀ (k : ℕ) (ak : vector ℕ (k + 1)), vector ℕ (k + 2)) :
  vector ℕ (n + 1) := nat.rec_on n ⟨[a₀], by simp⟩ h

def vseq_triangle (n : ℕ) : vector ℕ (n + 1) :=
  nat.vec_seq n 0 (λ k ak, vector.cons (k + ak.head) ak)

example : ∃ h, vseq_triangle 5 = ⟨[10, 6, 3, 1, 0, 0], h⟩ := by simpa

end sequences_of_vectors

universe u

section recursion_in_general

@[elab_as_eliminator]
def nat.rec_on' {C : ℕ → Sort u} (n : ℕ) (h₀ : C 0) (h₁ : ∀ (k : ℕ), C k → C k.succ) : C n :=
nat.rec_on n h₀ h₁

def vseq1 (n : ℕ) : vector ℕ n := nat.rec_on' n vector.nil (λ k seq_k, vector.cons (k*k) seq_k)

def seq (n : ℕ) : ℕ := nat.rec_on' n 6 (λ k seq_k, 5 + 2 * seq_k)

def add_one (n : ℕ) : ℕ := nat.rec_on n 1 (λ k ih, succ ih)

def add_one' (n : ℕ) : ℕ := @nat.rec_on (λ x, ℕ) n 1 (λ k ih, succ ih)

def add_two (n : ℕ) : ℕ := nat.rec_on n 2 (λ k ih, succ ih)

example : add_one 4 = 5 := rfl

example : add_two 4 = 6 := rfl

def myadd (m n : ℕ) : ℕ := nat.rec_on n m (λ k ih, succ ih)

example : myadd 11 5 = 16 := rfl

example : ∀ n, add_two n = myadd 2 n := λ n, rfl

end recursion_in_general

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