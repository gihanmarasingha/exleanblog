import data.nat.basic tactic data.nat.parity

namespace exlean

namespace wf_exlean

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

def myF : Π x : ℕ, (Π (y : ℕ), y < x → ℕ) → ℕ :=
begin
  intros x h,
  cases x with a,
  { exact 0, },
  { exact 1 + h (a.succ / 2) (div_two_lt (nat.succ_pos a)), },
end

def myF' : Π x : ℕ, (Π (y : ℕ), y < x → ℕ) → ℕ :=
λ x, nat.cases_on x (λ h, 0) (λ a h, 1 + h (a.succ / 2) (div_two_lt (nat.succ_pos a)))

def myF'' (x : ℕ) (h : Π (y : ℕ), y < x → ℕ) : ℕ :=
if h₂ : 0 < x then
  1 + h (x / 2) (div_two_lt h₂)
else 0

def lg := well_founded.fix nat.lt_wf myF'

def lg' : ℕ → ℕ
| x :=
  if h₂ : 0 < x then
    have x / 2 < x, from div_two_lt h₂,
    1 + lg' (x/2)
  else 0

/- def lg_zero_aux : ∀ x, x = 0 → lg' x = 0
| x := λ h, by { rw [lg', if_neg], rw h, exact nat.not_lt_zero 0, } -/

def lg_zero : lg' 0 = 0 := by { rw [lg', if_neg], intro h, exact nat.not_lt_zero 0 h }

def lg_one : lg' 1 = 1 := by { rw [lg', if_pos]; norm_num, rw lg_zero }

def lg_ineq : ℕ → Prop := λ n, n + 1 < 2 ^ lg' (n+1)

lemma lt_mul_two {m : ℕ} (h : 0 < m) : m < 2 * m :=
begin
  induction h with a hle ih,
  { norm_num, },
  { simp only [nat.succ_eq_add_one], linarith, }
end

lemma pred_lt_mul_two {m : ℕ} (h : 0 < m) : m.pred < 2 * m :=
begin
  induction h with a hle ih,
  { norm_num, },
  { simp only [nat.pred_succ, nat.succ_eq_add_one], linarith, }
end

lemma two_mul_succ_div_two {m : ℕ} : (2 * m + 1) / 2 = m :=
begin
  rw [nat.succ_div, if_neg],
  { norm_num, },
  { rintros ⟨k, h⟩,
    revert m, 
    induction k with k ih,
    { intros m h, linarith, },
    { intros m h, 
      cases m; simp only [nat.succ_eq_add_one] at h,
      { linarith, },
      { refine @ih m _, linarith }, },},
end

example (a : ℕ) : 2 * a / 2 = a := nat.mul_div_cancel_left _ (show 0 < 2, by linarith)

def lg_lemma (x : ℕ) (h : Π (y : ℕ), y < x → lg_ineq y) : lg_ineq x :=
if h₂ : 0 < x then
begin
  dsimp [lg_ineq] at h ⊢,
  cases (nat.even_or_odd x) with h₃ h₃,
  { cases h₃ with m h₃, rw h₃ at h₂ h ⊢, clear h₃,
    have h₄ : 0 < m, linarith,
    specialize h m.pred (pred_lt_mul_two h₄),
    rw [lg', if_pos],
    { rw two_mul_succ_div_two, 
      simp only [←nat.succ_eq_add_one] at h,
      rw (nat.succ_pred_eq_of_pos h₄) at h,
      have h₅ : 2 * m < 2 ^ (1 + lg' m),
      { rw [pow_add], linarith, },
      have h₆ : 2 * m + 1 < 2 ^ (1 + lg' m) ∨ 2 * m + 1 = 2 ^ (1 + lg' m) := lt_or_eq_of_le h₅,
      cases h₆,
      { exact h₆, },
      { rw [pow_add, pow_one] at h₆, linarith, }, },
    linarith, }, 
  { cases h₃ with m h₃, rw h₃ at h₂ h ⊢, clear h₃,
    specialize h m (by linarith),
    rw [lg', if_pos],
    { rw (show 2 * m + 1 + 1 = 2 * (m + 1), by linarith),
      rw nat.mul_div_cancel_left _ (show 0 < 2, by norm_num),
      rw pow_add, linarith, },
    { linarith, },
  
  }, -- take `y + 1 = (x+1)/2`.
end
else
begin
  have h₂ : x = 0, linarith, rw h₂, dsimp [lg_ineq],
  simp only [zero_add], rw lg_one, norm_num,
end


end wf_exlean

end exlean