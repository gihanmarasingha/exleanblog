import data.nat.prime

/-
We prove that sqrt 2 is irrational. To make things simple, we work with natural numbers instead
of rational numbers. The idea is to derive a contradiction from the assumption that
`(a^2 = 2 * (b ^ 2))` for coprime natural nubmers `a` and `b`.
-/

-- First an auxiliary result to show `2 ∣ x` if `x * x = 2 * y`.
lemma aux {x y : ℕ} (h : x * x = 2 * y) : 2 ∣ x :=
(or_self (2 ∣ x)).mp $ (nat.prime.dvd_mul nat.prime_two).mp ⟨y, h⟩

-- Proof of the irrationality of sqrt 2.
example (a b : ℕ) (cop : nat.coprime a b) : ¬(a^2 = 2*b^2) :=
begin
  simp only [pow_two],
  intro h,
  have twodiva : 2 ∣ a := aux h,
  have twodiva' := twodiva, -- make a copy!
  cases twodiva' with m hm,
  rw [hm, mul_assoc] at h,
  have hdiv : m * (2* m) = b * b, from mul_left_cancel' two_ne_zero h,
  rw [mul_comm, mul_assoc] at hdiv,
  have twodivb : 2 ∣ b := aux hdiv.symm,
  exact nat.not_coprime_of_dvd_of_dvd one_lt_two twodiva twodivb cop,
end
