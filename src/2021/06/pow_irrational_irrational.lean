import tactic data.rat data.nat.prime data.real.irrational
import analysis.special_functions.pow

open real

/-
We show there exist irrational numbers `a` and `b` such that `a ^ b` is rational.
-/

lemma ss_nat : sqrt 2 ^ 2 = 2 := sq_sqrt zero_le_two

lemma sq_sqrt2 : (sqrt 2)^(2 : ℝ) = 2 := by { conv_rhs { rw ←ss_nat}, simp [←rpow_nat_cast] }

-- A proof using `convert`.
example : ∃ a b : ℝ, irrational a ∧ irrational b ∧ ¬(irrational (a ^ b)) :=
begin
  have irrs2 := irrational_sqrt_two,
  by_cases h : irrational ((sqrt 2)^(sqrt 2)),
  { use [(sqrt 2)^(sqrt 2), sqrt 2],
    split, { exact h }, clear h,  split, { exact irrs2 },
    rw [←rpow_mul (sqrt_nonneg 2), ←pow_two, ss_nat, sq_sqrt2],
    have := rat.not_irrational 2, simpa, },
  { use [sqrt 2, sqrt 2], tauto, }
end