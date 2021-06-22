import data.nat.basic tactic data.nat.parity

namespace exlean

namespace wf_exlean

section logarithms

/-!
## Logarithms

We define a function `lg` that is (roughly) the base-2 logarithm. More precisely,

  `(n + 1) < 2 ^ lg (n + 1) ≤ 2 * (n + 1)`

for every `n : ℕ`. We prove the first of these inequalities.
-/

/--
`div_two_lt` is vital for our application of well-founded recursion.
-/
lemma div_two_lt {x : ℕ} (h : 0 < x) : x / 2 < x :=
begin
  induction h with a hle ih, -- Note the use of induction on `h`!
  { exact nat.zero_lt_one, },
  { rw [nat.succ_div, nat.succ_eq_add_one], 
    refine add_lt_add_of_lt_of_le ih _,
    have h : ite (2 ∣ a + 1) 1 0 = 1 ∨ ite (2 ∣ a + 1) 1 0 = 0 :=
    or.elim (em (2 ∣ a + 1)) (λ k₂, or.inl $ if_pos k₂) (λ k₂, or.inr $ if_neg k₂),
    cases h; rw h,
    { exact nat.zero_le 1, } },
end

/- 
def myF : Π x : ℕ, (Π (y : ℕ), y < x → ℕ) → ℕ :=
λ x, nat.cases_on x (λ h, 0) (λ a h, 1 + h (a.succ / 2) (div_two_lt (nat.succ_pos a))) -/

/--
`myF x h` gives the value of `lg x` where `h y` is `lg y` for `y < x`.
-/
def myF (x : ℕ) (h : Π (y : ℕ), y < x → ℕ) : ℕ :=
if h₂ : 0 < x then
  1 + h (x / 2) (div_two_lt h₂)
else 0

/-!
We prove that `myF` leads to well-founded recursive definition, which we call `lg_by_hand`.
-/

/--
`lg_by_hand x = floor (log₂ x) + 1`
-/
def lg_by_hand := well_founded.fix nat.lt_wf myF

/-!
`lg` is (extensionally) equal to `lg_by_hand`. Rather than using `well_founded.fix` and an
auxiliary function (such as `myF` above), we use the equation compiler to define the function
in one step.
-/

/--
`lg x = floor (log₂ x) + 1`
-/
def lg : ℕ → ℕ
| x :=
  if h₂ : 0 < x then
    have x / 2 < x, from div_two_lt h₂,
    1 + lg (x/2)
  else 0

/-!
### Proving log inequalities

We now show  `(n + 1) < 2 ^ lg (n + 1) ≤ 2 * (n + 1)` for each `n : ℕ`. The proof involves
well-founded recursion.
-/

def lg_zero : lg 0 = 0 := by { rw [lg, if_neg], intro h, exact nat.not_lt_zero 0 h }

def lg_one : lg 1 = 1 := by { rw [lg, if_pos]; norm_num, rw lg_zero }

/-!
`pred_lt_mul_two` is used later to show the recursion is well-founded.
-/
lemma pred_lt_mul_two {m : ℕ} (h : 0 < m) : m.pred < 2 * m :=
by { have : m.pred < m, { apply nat.pred_lt, linarith, }, linarith }

lemma two_mul_succ_div_two {m : ℕ} : (2 * m + 1) / 2 = m :=
begin
  rw [nat.succ_div, if_neg], norm_num,
  rintros ⟨k, h⟩, exact nat.two_mul_ne_two_mul_add_one h.symm,
end

def lg_ineq : ℕ → Prop := λ n, n + 1 < 2 ^ lg (n + 1)

/--
`lg_lemma_aux` is an auxiliary lemma used to show `lg x` satisfies the desired lower bound on
the assumpion that `lg y` also satisfies the correct bound, for every `y < x`.
-/
lemma lg_lemma_aux (x : ℕ) (h : Π (y : ℕ), y < x → lg_ineq y) : lg_ineq x :=
if h₂ : 0 < x then
begin
  dsimp [lg_ineq] at h ⊢,
  cases (nat.even_or_odd x) with h₃ h₃,
  { cases h₃ with m h₃, rw h₃ at h₂ h ⊢, clear h₃,
    have h₄ : 0 < m, linarith,
    specialize h m.pred (pred_lt_mul_two h₄),
    rw [lg, if_pos], swap, linarith,
    rw two_mul_succ_div_two, 
    simp only [←nat.succ_eq_add_one] at h, rw (nat.succ_pred_eq_of_pos h₄) at h,
    have h₅ : 2 * m < 2 ^ (1 + lg m), { rw [pow_add], linarith, },
    have h₆ : 2 * m + 1 < 2 ^ (1 + lg m) ∨ 2 * m + 1 = 2 ^ (1 + lg m) := lt_or_eq_of_le h₅,
    cases h₆, { exact h₆, }, { rw [pow_add, pow_one] at h₆, linarith, }, }, 
  { cases h₃ with m h₃, rw h₃ at h₂ h ⊢, clear h₃,
    specialize h m (by linarith),
    rw [lg, if_pos], swap, linarith,
    rw (show 2 * m + 1 + 1 = 2 * (m + 1), by linarith),
    rw nat.mul_div_cancel_left _ (show 0 < 2, by norm_num),
    rw pow_add, linarith, }, 
end
else by { dsimp [lg_ineq], rw [(show x = 0, by linarith), zero_add, lg_one], norm_num, }

/--
`lg_lemma` is the lower bound result for `lg x`. It uses well-founded recursion and `lg_lemma_aux`.
-/
lemma lg_lemma : ∀ (x : ℕ), x + 1 < 2 ^ lg (x + 1) := well_founded.fix nat.lt_wf lg_lemma_aux

/--
`lg_lemma'` is the lower bound result for `lg x`. In contrast to `lg_lemma`, this proof uses the
equation compiler to bypass the application of `well_founded.fix`.

At two points in the proof, we supply inequalities needed to show that the recursive application
is decreasing. These must be provided in term mode.
-/
lemma lg_lemma' : ∀ (x : ℕ), x + 1 < 2 ^ lg (x + 1)
| x :=
if h₂ : 0 < x then or.elim (nat.even_or_odd x)
(λ ⟨m, h₃⟩, have h₄ : 0 < m, by linarith,
have m.pred < x := h₃.symm ▸ pred_lt_mul_two h₄, -- needed for wf recusion
begin
  rw h₃ at h₂ ⊢, clear h₃,
  specialize lg_lemma' m.pred, rw [lg, if_pos], swap, linarith,
  rw two_mul_succ_div_two, 
  simp only [←nat.succ_eq_add_one] at lg_lemma', rw (nat.succ_pred_eq_of_pos h₄) at lg_lemma',
  have h₅ : 2 * m < 2 ^ (1 + lg m), { rw [pow_add], linarith, },
  have h₆ : 2 * m + 1 < 2 ^ (1 + lg m) ∨ 2 * m + 1 = 2 ^ (1 + lg m) := lt_or_eq_of_le h₅,
  cases h₆, { exact h₆, }, { rw [pow_add, pow_one] at h₆, linarith, },
end)
(λ ⟨m, h₃⟩, have m < x, by { rw h₃, linarith }, -- needed for wf recursion
begin
  specialize lg_lemma' m, rw h₃ at h₂ ⊢, clear h₃,
  rw [lg, if_pos], swap, linarith, 
  rw (show 2 * m + 1 + 1 = 2 * (m + 1), by linarith),
  rw nat.mul_div_cancel_left _ (show 0 < 2, by norm_num), rw pow_add, linarith, 
end)
else by { rw [(show x = 0, by linarith), zero_add, lg_one], norm_num }

end logarithms

end wf_exlean

end exlean