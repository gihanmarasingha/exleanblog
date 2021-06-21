import data.nat.basic tactic

namespace exlean

namespace wf_exlean

lemma div_two_lt {x : ℕ} (h : 0 < x) : x / 2 < x :=
begin
  induction h with a hle ih,
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

def lg_zero_aux : ∀ x, x = 0 → lg' x = 0
| x := λ h, by { rw [lg', if_neg], rw h, exact nat.not_lt_zero 0, }

def lg_zero : lg' 0 = 0 := lg_zero_aux 0 rfl

-- For some weird reason, we need to do pattern matching when proving theorems like the
-- one below. It's awkward, but it works.
def lg_one_aux : ∀ x, x = 1 → lg' x = 1
| x := λ h,
begin
  rw [lg', if_pos], rw h, rw [lg', if_neg],
  { exact nat.not_lt_zero 0, },
  { rw h, exact nat.zero_lt_one, },
end

def lg_one : lg' 1 = 1 := lg_one_aux 1 rfl

def lg_ineq : ℕ → Prop := λ n, n + 1 < 2 ^ lg' (n+1)

def lg_lemma (x : ℕ) (h : Π (y : ℕ), y < x → lg_ineq y) : lg_ineq x :=
if h₂ : 0 < x then
begin
  dsimp [lg_ineq] at *,
  by_cases even x,
  { sorry }, -- here `x = 2m`. Take `y = m`.
  { sorry }, -- take `y + 1 = (x+1)/2`.
end
else
begin
  have h₂ : x = 0, linarith, rw h₂, dsimp [lg_ineq],
  simp only [zero_add], rw lg_one, norm_num,
end

end wf_exlean

end exlean