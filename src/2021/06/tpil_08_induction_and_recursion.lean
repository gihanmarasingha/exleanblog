import tactic

example {α : Type*} (p q : α → Prop) :
  (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
| (Exists.intro x (or.inl px)) := or.inl (exists.intro x px)
| (Exists.intro x (or.inr qx)) := or.inr (exists.intro x qx)

namespace pattern_matching

  def bnot : bool → bool
  | tt := ff
  | ff := tt

  #print bnot._main

  theorem bnot_bnot : ∀ (b : bool), bnot (bnot b) = b
  | tt := rfl    -- proof that bnot (bnot tt) = tt
  | ff := rfl    -- proof that bnot (bnot ff) = ff

  example (p q : Prop) : p ∧ q → q ∧ p
  | (and.intro h₁ h₂) := and.intro h₂ h₁

  example (p q : Prop) : p ∨ q → q ∨ p
  | (or.inl hp) := or.inr hp
  | (or.inr hq) := or.inl hq

  open nat

  def sub2 : ℕ → ℕ
  | 0     := 0
  | 1     := 0
  | (a+2) := a

  example : sub2 0 = 0 := rfl
  example : sub2 1 = 0 := rfl
  example (a : nat) : sub2 (a + 2) = a := rfl

  example : sub2 5 = 3 := rfl

  #print sub2
  #print sub2._main

  #check @nat.rec_on
  #check @nat.cases_on 

  def {u} moop : Π {C : ℕ → Sort u} (n : ℕ), C 0 → (Π (m : ℕ), C m.succ) → C n := @nat.cases_on

  /-
  The defintion of `sub2` above is equivalent to `sub2'` below. Let's think about how this works.

  We use the `nat.cases_on` eliminator applied to `n`. Recall that `@nat.cases_on` has type

    `Π {C : ℕ → Sort u} (n : ℕ), C 0 → (Π (m : ℕ), C m.succ) → C n`

  In our application, `C : ℕ → Type` is the (dependent) function `λ (z : ℕ), ℕ`.

  Thus `C 0` is the type `ℕ` and `(Π (m : ℕ), C m.succ)` is `Π (m : ℕ), ℕ`, i.e. `ℕ → ℕ`.

  In the case where `n` is `0`, we return `0`, meaning that `sub2' 0 = 0`.

  Next, we must give a term of type `ℕ → ℕ` representing the function that takes `m` to
  `sub2' (succ m)`

  We next have a term of type `Π (n : ℕ), C n.succ`, where (in our case) `C : ℕ → Type` is the
  function `λ (z : ℕ), ℕ`. That is, we have a term of type `Π (n : ℕ) : ℕ`.
  
  Write `λ m, f m` for this function. We want `f 0 = 0` (i.e. `sub2' (succ 0) = 0`) and
  we want `f (succ p) = p` (i.e. we want `sub2' (succ (succ p)) = p`).

  So we take `f m` to be `nat.cases_on 0 (λ p, p)`.
  -/
  def sub2' (n : ℕ) : ℕ := nat.cases_on n 0 (λ m, nat.cases_on m 0 (λ p, p))

  /-
  The same function can be defined using `nat.rec_on`.
  -/
  def sub2'' (n : ℕ) : ℕ := nat.rec_on n 0 (λ m _, nat.rec_on m 0 (λ p _, p))

  example : sub2' 0 = 0 := rfl
  example (n : ℕ) : sub2' (succ n) = nat.cases_on n 0 (λ p, p) := rfl
  example (n : ℕ) : sub2' (succ 0) = 0 := rfl
  example (n : ℕ) : sub2' (succ (succ n)) = n := rfl

  lemma noo1 {α : Type*} (p q : α → Prop) :
    (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x)
  | (Exists.intro x (or.inl px)) := or.inl (exists.intro x px)
  | (Exists.intro x (or.inr qx)) := or.inr (exists.intro x qx)
 
  #print noo1

  /-
  Processing of multiple arguments sequentially.
  -/
  def foo : ℕ → ℕ → ℕ
  | 0     n     := 0
  | (m+1) 0     := 1
  | (m+1) (n+1) := 2

  /-
  Here we see the use of wildcards in defining binomial coefficients.
  -/
  def binom : ℕ → ℕ → ℕ
  | _     0     := 1
  | 0     (n+1) := 0
  | (n+1) (k+1) := binom n k + binom n (k+1)

end pattern_matching

namespace wildcards_and_overlapping_patterns

  /-
  We can use overlapping patterns to define binomial coefficients.
  -/
  def binom : ℕ → ℕ → ℕ
  | _     0     := 1
  | 0     _     := 0
  | (n+1) (k+1) := binom n k + binom n (k+1)

  -- Note that the first of the patterns above is used in computing `binom 0 0`.
  example : binom 0 0 = 1 := rfl

  -- Every inhabited type has an arbitrary value. We can use this to define a function.
  def f1 : ℕ → ℕ → ℕ
  | 0  _  := 1
  | _  0  := 2
  | _  _  := arbitrary ℕ   -- the "incomplete" case

  example : f1 3 5 = arbitrary ℕ := rfl

  -- Here's a more general version.
  def f1' {R : Type} [inhabited R] : R := arbitrary R


end wildcards_and_overlapping_patterns

namespace structural_recursion_and_induction

  section addition_and_multiplication

  open nat

  def add : nat → nat → nat
  | m zero     := m
  | m (succ n) := succ (add m n)

    local infix ` + ` := add

    theorem add_zero (m : nat) : m + zero = m := rfl
    theorem add_succ (m n : nat) : m + succ n = succ (m + n) := rfl

    /-
    To understand the second line below, realise that the goal is to prove `0 + (succ n) = succ n`.
    Definitionally, `0 + (succ n) = succ (0 + n)`, so we must prove `succ (0 + n) = succ n`.
    This is where `congr_arg` comes into play.
    -/
    theorem zero_add : ∀ n, zero + n = n
    | zero     := rfl
    | (succ n) := congr_arg succ (zero_add n)
    
    def mul : nat → nat → nat
    | n zero     := zero
    | n (succ m) := mul n m + n

    /-
    The idea with the function defintion below is that we fix a parameter `m` and then define
    a function `mul' : nat → nat` that represents 'muliplty by m'.
    -/
    def mul' (m : ℕ) : nat → nat
    | zero       := zero
    | (succ n)   := (mul' n) + m

  end addition_and_multiplication

  /-
  See the file `08b_course_of_values_recursion.lean` for a discussion of course-of-values recursion.
  -/

end structural_recursion_and_induction

namespace well_founded_recursion

  universe u

  /-
  Let `α : Sort u` be a sort and let `r : α → α → Prop` be a relation. Then `acc r` is an inductive
  family of types.

  For each `x : α`, the type `acc r x` represents the notion that `x` is 'accessible' wrt the
  relation `r`. For `x` to be accessible means that for every `y : α`, if `r y x`, then `y`
  is accessible. This notion is expressed via the single contructor of `acc`.
  -/
  inductive acc {α : Sort u} (r : α → α → Prop) : α → Prop
  | intro (x : α) (h : ∀ y, r y x → acc y) : acc x


  /-
  As a practical example, we'll take `α` to be `ℕ` and `r` to be the less than relation on `ℕ `,
  We give several proofs of `acc r 0`.

  Assuming `y : ℕ` and `hy : α, y < 0`, we must proove `acc r y`. But `hy` leads to a contradiction.
  
  More generally, whatever relation `r` we have, if `x` has no 'predecessor', then we can deduce
  `acc r x`.
  -/

  def r := λ (m n : ℕ), m < n

  example : acc r 0 := acc.intro 0 (λ y hy, absurd hy (nat.not_lt_zero y)) -- most detailed proof.
  example : acc r 0 := ⟨0, λ y hy, absurd hy (nat.not_lt_zero y)⟩ -- anonymous constructor.
  lemma acc_lt_zero : acc r 0 := ⟨0, λ y hy, by {unfold r at hy, linarith}⟩ -- Using `linarith`.
  example : acc r 0 := -- Tactic-based proof.
  begin
    existsi 0, -- `split` also works
    intros y hy, unfold r at hy, linarith,
  end
  
  /-
  Using the above, we'll prove that `1` is accessible.
  -/
  lemma acc_lt_one : acc r 1 := ⟨1,
    λ y hy,
    have h : y = 0, from nat.le_zero_iff.mp (nat.lt_succ_iff.mp hy),
    h.symm ▸ acc_lt_zero ⟩

  #check @nat.case_strong_induction_on
  #check @nat.strong_induction_on

  /-
  More generally, we'll show that every natural number is accessible. The proof below seems like a
  bit a of a cheat because the the strong inductionn principle is virtually equivalent to the
  result we're trying to prove!

  I see that the proof of `nat.strong_rec_on` uses a decidability prove. Does this depend
  ultimately on `acc`? I don't know.
  -/
  lemma acc_lt_nat (n : ℕ) : acc r n := nat.strong_induction_on n (λ k hk, ⟨k, hk⟩)

  /-
  Intuitively, `0 : ℤ` is *not* accessible wrt the less-than relation on `ℤ`, though I don't know
  how to prove this!
  -/


  

end well_founded_recursion