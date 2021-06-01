import tactic data.vector


namespace exlean 

open nat

section induction_on_nat

@[elab_as_eliminator, reducible]
def nat.ind (P : ℕ → Prop) (n : ℕ) (h₀ : P 0) (h₁ : ∀ (k : ℕ), P k → P k.succ) : P n :=
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

example : ℕ := succ (succ zero)

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
def nat.nat_seq (n : ℕ) (h₀ : ℕ) (h₁ : Π (k : ℕ), ℕ → ℕ) : ℕ :=
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

def natvec (k : ℕ) := vector ℕ (succ k)

-- A principle for defining sequences of vectors of natural numbers. The `n`th term in the sequence
-- is a vector of length `n + 1`.
def nat.vec_seq (n : ℕ) (a₀ : natvec 0) (h : Π (k : ℕ) (ak : natvec k), natvec (succ k)) :
  natvec n := nat.rec_on n a₀ h

-- A sequence of triangular numbers.
def vseq_triangle (n : ℕ) : natvec n :=
  nat.vec_seq n ⟨[0], rfl⟩ (λ k ak, vector.cons (k + ak.head) ak)

example : vseq_triangle 5 = ⟨[10, 6, 3, 1, 0, 0], _⟩ := rfl

-- A principle for defining sequences of vectors. The `n`th term in the sequence is a vector of
-- length `n`.
def nat.vec_seq_simple (n : ℕ) (h : Π (k : ℕ) (ak : vector ℕ k), vector ℕ (k+1)) : vector ℕ n :=
  nat.rec_on n vector.nil h

def vseq (n : ℕ) : vector ℕ n := nat.vec_seq_simple n (λ k ak, vector.cons (k*k) ak)

/--
A slighly different definition of a sequence of triangular numbers. We begin with an auxiliary function.
**Note** this is a bit of a cheat as pattern matching of course involves recursion. We'll redo this
in the next section.
-/
def next_vec : Π (k : ℕ), vector ℕ k → vector ℕ (k+1)
| 0       _   := ⟨[0], rfl⟩
| m@(a+1) am  := vector.cons (m + am.head) am

def vseq_triangle' (n : ℕ) : vector ℕ n :=
  nat.vec_seq_simple n next_vec

def vseq_triangle'' (n : ℕ) : vector ℕ n :=
  nat.vec_seq_simple n (λ k,
  match k with
  | 0       := λ ak, ⟨[0], rfl⟩
  | m@(a+1) := λ am, vector.cons (m + am.head) am
  end )

example : vseq_triangle' 6 = ⟨[15, 10, 6, 3, 1, 0], _⟩ := rfl

#reduce vseq_triangle' 1

/-
Using the above idea, we can define the Fibonacci sequence. Again, we can do this with `nat.rec_on`
as we'll see later.
-/
def next_fib_cheat : Π (k : ℕ), vector ℕ k → vector ℕ (k+1)
| 0       _   := ⟨[1], rfl⟩
| 1       _   := ⟨[1,1], rfl⟩
| m@(a+2) am  := vector.cons (am.head + am.tail.head) am

def vseq_fib_cheat (n : ℕ) : vector ℕ n :=
  nat.vec_seq_simple n next_fib_cheat

example : vseq_fib_cheat 7 = ⟨[13, 8, 5, 3, 2, 1, 1], _⟩ := rfl

end sequences_of_vectors

universe u

section recursion_in_general

@[elab_as_eliminator, reducible]
def nat.rec_on' {C : ℕ → Sort u} (n : ℕ) (h₀ : C 0) (h₁ : Π (k : ℕ), C k → C k.succ) : C n :=
nat.rec_on n h₀ h₁

example (P : ℕ → Prop) (n : ℕ) (h₀ : P 0) (h₁ : ∀ (k : ℕ), P k → P k.succ) : 
  @nat.ind P n h₀ h₁ = @nat.rec_on P n h₀ h₁ := rfl

example (n : ℕ) (a₀ : ℤ) (h : ∀ (k : ℕ) (ak : ℤ), ℤ) :
  nat.int_seq n a₀ h = @nat.rec_on' (λ (k : ℕ), ℤ) n a₀ h := rfl

example (n : ℕ) (a₀ : natvec 0) (h : Π (k : ℕ) (ak : natvec k), natvec (succ k)) : 
  nat.vec_seq n a₀ h = @nat.rec_on' natvec n a₀ h := rfl

def next_vec' : Π (k : ℕ), vector ℕ k → vector ℕ (k+1) :=
begin
  intro k,
  refine nat.rec_on' k _ _,
  { intro am, exact ⟨[0], rfl⟩, },
  { intros m h am, exact vector.cons (m + am.head) am },
end

def next_vec'' : Π (k : ℕ), vector ℕ k → vector ℕ (k+1) :=
λ k, nat.rec_on k (λ am, ⟨[0], rfl⟩) (λ m h am, vector.cons (m + am.head) am)

def next_vec''' : Π (k : ℕ), vector ℕ k → vector ℕ (k+1) :=
λ k, nat.rec_on k (λ am, ⟨[0], rfl⟩) (λ m h am, vector.cons (m + am.head) am)

def vseq_triangle''' (n : ℕ) : vector ℕ n :=
  nat.vec_seq_simple n (λ k, nat.rec_on k (λ am, ⟨[0], rfl⟩) (λ m h am, vector.cons (m + am.head) am))

def vseq_triangle'''' (n : ℕ) : vector ℕ n :=
  nat.rec_on n vector.nil next_vec''

def next_fib : Π (k : ℕ), vector ℕ k → vector ℕ (k+1) :=
begin
  intro k,
  refine nat.rec_on' k _ _,
  { intro am, exact ⟨[1], rfl⟩, },
  { intros m h am,
    refine nat.rec_on' m _ _,
    { exact ⟨[1, 1], rfl⟩ },
    { intros c ac, exact vector.cons (ac.head + ac.tail.head) ac }, },
end

def next_fib'' : Π (k : ℕ), vector ℕ k → vector ℕ (k+1) :=
λ k, nat.rec_on' k (λ _, ⟨[1], rfl⟩) (λ m _ _, nat.rec_on' m ⟨[1,1], rfl⟩
  (λ _ ac, vector.cons (ac.head + ac.tail.head) ac))

def vfib (n : ℕ) : vector ℕ n :=
  nat.rec_on n vector.nil next_fib

lemma vfib_succ (n : ℕ) : vfib (succ (succ (succ n))) =
  vector.cons ( (vfib (succ (succ n))).head + (vfib (succ (succ n))).tail.head)
    (vfib (succ (succ n))) := rfl

lemma vfib_succ_tail (n : ℕ) : (vfib (succ n)).tail = vfib n :=
begin
  refine nat.rec_on n rfl _,
  intro k,
  refine nat.rec_on k _ _,
  { intro h, refl, },
  { intros m ih, rw vfib_succ, simp, },
end
  
lemma vfib_formula (n : ℕ) :
  (vfib (n+3)).head = (vfib (n+2)).head + (vfib (n+1)).head :=
by simp [vfib_succ, vfib_succ_tail]

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

end exlean