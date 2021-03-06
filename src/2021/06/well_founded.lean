import tactic data.nat.parity tactic.induction

import init.meta.well_founded_tactics

namespace exlean

namespace wf_exlean

/-
# Well-founded recursion
-/

section logarithms

/-!
## Logarithms and basic ideas

We define a function `lg` that is (roughly) the base-2 logarithm. More precisely,

  `(n + 1) < 2 ^ lg (n + 1) ≤ 2 * (n + 1)`

for every `n : ℕ`. We prove the first of these inequalities and introduce techniques for
working with well-founded recursion.
-/

/-!
### Definitions and simple proofs

Here are definitions of `lg` (and extensionally-equal variants) via `well_founded.fix` and
via the equation compiler. We prove such simple results as `lg 1 = 1`.
-/

/--
`myF x h` gives the value of `lg x` where `h y` is `lg y` for `y < x`.
-/
def myF : Π (x : ℕ) (h : Π (y : ℕ), y < x → ℕ), ℕ
| 0 _ := 0
| (x + 1) h := 1 + h ((x + 1) / 2) (nat.div_lt_self' x 0)

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
| 0 := 0
| (x + 1) := have (x + 1) / 2 < (x + 1), from nat.div_lt_self' _ _,
    1 + lg ((x + 1)/2)

def jane : ℕ → ℕ
| 0 := 2
| (x + 1) := 3 * jane x

example : jane 3 = 54 := rfl

lemma lg_zero : lg 0 = 0 := by { rw lg }

lemma lg_zero' : lg 0 = 0 := well_founded.fix_eq _ _ _

example : lg_by_hand 0 = well_founded.fix nat.lt_wf myF 0 := rfl

lemma lg_one : lg 1 = 1 := by { erw [lg, lg_zero] }

lemma lg_by_hand_eq : ∀ x, lg_by_hand x = myF x (λ y h, lg_by_hand y) := well_founded.fix_eq _ _

lemma lg_zero_bh : lg_by_hand 0 = 0 := lg_by_hand_eq 0

lemma lg_one_bh : lg_by_hand 1 = 1 := by { erw [lg_by_hand_eq, myF, lg_zero_bh] }

section exercises

/-!
### Some basic exercises

The exercises (solutions here, questions in the blog) are to define a function described
mathematically and then prove simple equations involving the function.
-/

def ex1 : ℕ → ℕ
| 0 := 1
| (x + 1) := have (x + 1) / 3 < x + 1, from nat.div_lt_self' _ _,
    (x + 1) * ex1 ( (x + 1) / 3)

example : ex1 0 = 1 := by { rw ex1 }

example : ex1 2 = 2 := by { erw [ex1, ex1], norm_num }

example : ex1 4 = 4 := by { erw [ex1, ex1, ex1], norm_num }

def ex1_F : Π (x : ℕ) (h : Π (y : ℕ), y < x → ℕ), ℕ
| 0 _ := 1
| (x + 1) h := (x + 1) * (h ((x + 1)/3) (nat.div_lt_self' _ _))

def ex1' := well_founded.fix nat.lt_wf ex1_F

lemma ex1'_eq : ∀ x, ex1' x = ex1_F x (λ y h, ex1' y) := well_founded.fix_eq _ _

lemma ex1'_0 : ex1' 0 = 1 := ex1'_eq 0

lemma ex1'_4 : ex1' 4 = 4 := by { erw [ex1'_eq, ex1_F, ex1'_eq, ex1_F, ex1'_0], norm_num,  }

def ex2 : ℕ → ℕ
| n := if h : odd n ∨ n = 0 then 0 else
 have n / 2 < n, from
  nat.div_lt_self (nat.pos_of_ne_zero (not_or_distrib.mp h).2) (nat.le_refl 2),
  1 + ex2 (n / 2)

lemma ex2_4 : ex2 4 = 2 := by { erw [ex2, ex2, ex2], norm_num }

def ex2_F : Π (x : ℕ) (h : Π (y : ℕ), y < x → ℕ), ℕ
| n ih := if h : odd n ∨ n = 0 then 0 else
  1 + ih (n / 2) (nat.div_lt_self (nat.pos_of_ne_zero (not_or_distrib.mp h).2) (nat.le_refl 2))

def ex2' := well_founded.fix nat.lt_wf ex2_F

lemma ex2'_eq : ∀ x, ex2' x = ex2_F x (λ y h, ex2' y) := well_founded.fix_eq _ _

lemma ex2'_0 : ex2' 0 = 0 := ex2'_eq 0

lemma ex2'_1 : ex2' 1 = 0 := ex2'_eq 1

lemma ex2'_2 : ex2' 2 = 1 := by { erw [ex2'_eq, ex2_F, ex2'_1], norm_num }

lemma ex2'_4 : ex2' 4 = 2 := by { erw [ex2'_eq, ex2_F, ex2'_2], norm_num }

end exercises

section underhanded_tricks

/-!
### Underhanded tricks

Various tricks can be employed to simplify use of the equation compiler to define functions that
depend on well-founded recursion.
-/

def lg2 : ℕ → ℕ
| 0 := 0
| 1 := 0
| (n + 2) :=
  have h : (n + 2) / 2 = n / 2 + 1 :=
    nat.add_div_of_dvd_left (dvd_refl 2),
  have n / 2 + 1 < n + 2 := h ▸ nat.div_lt_self' _ _,
    1 + lg2 ((n + 2) / 2)

def lg2' : ℕ → ℕ
| n := if h : n ≤ 1 then 0 else
 have n / 2 < n, from
  nat.div_lt_self (by linarith) (nat.le_refl 2),
  1 + lg2' (n / 2)

def lg2'' : ℕ → ℕ
| n := if h : n ≤ 1 then 0 else
 have n / 2 < n, from nat.div_lt_self (by linarith) (nat.le_refl 2),
 by { exact 1 + lg2'' (n / 2) }

def lg2''' : ℕ → ℕ
| n := if h : n ≤ 1 then 0 else
begin
  exact have n / 2 < n,
    from nat.div_lt_self (by linarith) (nat.le_refl 2),
  1 + lg2''' (n / 2),
end

end underhanded_tricks

section proving_log_inequalities

/-!
### Proving log inequalities

We now show  `(n + 1) < 2 ^ lg (n + 1) ≤ 2 * (n + 1)` for each `n : ℕ`. The proof involves
well-founded recursion.
-/

lemma two_mul_succ_div_two {m : ℕ} : (2 * m + 1) / 2 = m :=
begin
  rw [nat.succ_div, if_neg], norm_num,
  rintros ⟨k, h⟩, exact nat.two_mul_ne_two_mul_add_one h.symm,
end

lemma two_mul_succ_succ {m : ℕ} : 2 * m + 1 + 1 = 2 * (m + 1) := by linarith

def lg_ineq (n : ℕ) : Prop := n + 1 < 2 ^ lg (n + 1)

/--
`lg_lemma_aux` is an auxiliary lemma used to show `lg x` satisfies the desired lower bound on
the assumpion that `lg y` also satisfies the correct bound, for every `y < x`.
-/

lemma lg_lemma_aux (x : ℕ) (h : Π (y : ℕ), y < x → lg_ineq y) : lg_ineq x :=
begin
  cases x,
  { rw [lg_ineq, lg_one], norm_num, }, -- base case
  dsimp [lg_ineq] at h ⊢,
  rcases nat.even_or_odd x with ⟨m, rfl⟩ | ⟨m, rfl⟩,
  { have h₄ : m < 2 * m + 1, by linarith,
    specialize h m h₄, rw [nat.succ_eq_add_one, lg, pow_add],
    rw two_mul_succ_succ, norm_num, exact h, },
  { have h₄ : m < 2 * m + 1 + 1, by linarith,
    specialize h m h₄, rw [lg, pow_add, nat.succ_eq_add_one],
    rw [two_mul_succ_succ, two_mul_succ_div_two], linarith, }, 
end

/--
`lg_lemma` is the lower bound result for `lg x`. It uses well-founded recursion and `lg_lemma_aux`.
-/
lemma lg_lemma : ∀ (x : ℕ), x + 1 < 2 ^ lg (x + 1) := well_founded.fix nat.lt_wf lg_lemma_aux

/--
`lg_lemma2` is the lower bound result for `lg x`. In contrast to `lg_lemma`, this proof uses the
equation compiler to bypass the application of `well_founded.fix`.

At two points in the proof, we supply inequalities needed to show that the recursive application
is decreasing. These must be provided in term mode.
-/
lemma lg_lemma2 : ∀ (x : ℕ), x + 1 < 2 ^ lg (x + 1)
| 0 := by { rw lg_one, norm_num, }
| (x + 1) := or.elim (nat.even_or_odd x)
( λ ⟨m, hm⟩,
  have m < x + 1, by linarith, -- needed for wf recursion
  begin
    specialize lg_lemma2 m, rw [hm, lg, pow_add],
    rw two_mul_succ_succ, norm_num, exact lg_lemma2,
  end )
( λ ⟨m, hm⟩,
  have m < x + 1, by linarith, -- needed for wf recursion
  begin
    specialize lg_lemma2 m, rw [hm, lg, pow_add],
    rw [two_mul_succ_succ, two_mul_succ_div_two], linarith,
  end )

/-
`lg_lemma2` pushes more of the proof into tactic mode, only coming out of tactic mode to
prove the recursive application is decreasing.
-/
lemma lg_lemma2' : ∀ (x : ℕ), x + 1 < 2 ^ lg (x + 1)
| 0 := by { rw lg_one, norm_num, }
| (x + 1) :=
begin
  cases (nat.even_or_odd x),
  { rcases h with ⟨m, hm⟩,
    rw [hm, lg, pow_add],
    rw two_mul_succ_succ, norm_num,
    exact have m < x + 1, by linarith,
      lg_lemma2' m, },
  { rcases h with ⟨m, hm⟩,
    rw [hm, lg, pow_add, two_mul_succ_succ, two_mul_succ_div_two], 
    exact have m < x + 1, by linarith,
     show _, by { specialize lg_lemma2' m, linarith }, }
end

/--
`lg_lemma2''` is a proof of the lower bound via `using_well_founded`.
-/
lemma lg_lemma2'' : ∀ (x : ℕ), x + 1 < 2 ^ lg (x + 1)
| 0 := by { rw lg_one, norm_num, }
| (x + 1) :=
begin
  cases (nat.even_or_odd x),
  { rcases h with ⟨m, hm⟩, specialize lg_lemma2'' m, rw [hm, lg, pow_add],
    rw two_mul_succ_succ, norm_num, exact lg_lemma2'', },
  { rcases h with ⟨m, hm⟩,
    specialize lg_lemma2'' m, rw [hm, lg, pow_add],
    rw [two_mul_succ_succ, two_mul_succ_div_two], linarith }
end
using_well_founded { dec_tac := `[exact show m < x + 1, by linarith] }

end proving_log_inequalities

section exercises

/-!
### Exercises

The first exercise is a trivial modification of `lg_lemma2''`, but for the upper bound.
The second concerns the lower bound for the `lg2` function and requires more thought.
-/

lemma lg_ub : ∀ (x : ℕ), 2 ^ lg (x + 1) ≤ 2 * (x + 1)
| 0 := by { rw lg_one, norm_num, }
| (x + 1) :=
begin
  cases (nat.even_or_odd x),
  { rcases h with ⟨m, hm⟩, specialize lg_ub m, rw [hm, lg, pow_add],
    rw two_mul_succ_succ, norm_num, exact lg_ub, },
  { rcases h with ⟨m, hm⟩,
    specialize lg_ub m, rw [hm, lg, pow_add],
    rw [two_mul_succ_succ, two_mul_succ_div_two], linarith }
end
using_well_founded { dec_tac := `[exact show m < x + 1, by linarith] }

example (a b c : ℕ) : (2 * a + 2) / 2 = a + 1 := by norm_num

/-!
In the proof below, the `dec_tac` term uses a tactic combinator. Is there a better approach?
-/

 lemma lg2_lb : ∀ (x : ℕ), (x + 1) < 2 * 2 ^ lg2 (x + 1)
| 0 := by { rw lg2, norm_num }
| 1 := by { erw [lg2, lg2], norm_num }
| (x + 2) :=
begin
  cases (nat.even_or_odd x),
  { rcases h with ⟨m, hm⟩, specialize lg2_lb m, rw [hm, lg2, pow_add],
    conv_rhs { rw [add_right_comm, two_mul_succ_succ, two_mul_succ_div_two], }, linarith },
  { rcases h with ⟨m, hm⟩, rw [hm, lg2, two_mul_succ_succ, pow_add, two_mul_succ_succ],
    rw nat.mul_div_cancel_left _ zero_lt_two, specialize lg2_lb (m + 1), linarith, }
end
using_well_founded { dec_tac :=
  `[ {exact show m + 1 < x + 2, by linarith} <|> exact show m < x + 2, by linarith ] } 

end exercises

end logarithms

section prime_factors

/-!
## Prime factors

The following is adapted from `data.nat.prime` in mathlib. Here the normal `<` relation isn't what
we want because we're computing `min_fac_aux k` using a value for `min_fac_aux (k + 2)`.

But clearly `k + 2 < k` is false! Instead, we use a relation generated by a 'measure', that is,
a function `f : α → ℕ`. In our case, we take `f` so that `f k = sqrt n + 2 - k`, where `n` is fixed.

Let `≺` denote the relation on `ℕ` generated by `f`. By definition, `a ≺ b` means `f a < f b`.
It's a theorem that for every measure `f`, the relation `≺` is well-founded.

We ask Lean to use this relation via the command

``using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ k, sqrt n + 2 - k)⟩]}``

What remains is to show that the recursive application in decreasing. Recall we want to define
`min_fac_aux k` in terms of `min_fac_aux (k + 2)`. We must show `f (k + 2) < f k`.

This is precisely the assertion of `min_fac_lemma`.
-/

open nat

lemma min_fac_lemma (n k : ℕ) (h : ¬ n < k * k) :
    sqrt n - k < sqrt n + 2 - k :=
begin
  rw nat.sub_lt_sub_right_iff,
  { exact lt_trans (lt_add_one _) (lt_add_one _) },
  { rw nat.le_sqrt, exact le_of_not_gt h },
end

def min_fac_aux (n : ℕ) : ℕ → ℕ | k :=
if h : n < k * k then n else
if k ∣ n then k else
have _ := min_fac_lemma n k h, 
min_fac_aux (k + 2)
using_well_founded {
  rel_tac := λ _ _,
    `[exact ⟨_, measure_wf (λ k, sqrt n + 2 - k)⟩]}

lemma min_fac_dvd (n : ℕ) : ∀ (k : ℕ), (min_fac_aux n k) ∣ n
| k := if h : n < k * k then by { rw min_fac_aux, simp [h] } else 
  if hk : k ∣ n then by { rw min_fac_aux, simp [h, hk] } else
  have _ := min_fac_lemma n k h, 
  by { rw min_fac_aux, simp [h, hk], exact min_fac_dvd (k+2) }
  using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ k, sqrt n + 2 - k)⟩]}

end prime_factors

section fermat_factorisation

/-
## Fermat factorisation

`fermat_fac n` returns a factor of `n` by Fermat factorisation.

It uses a function `fermat_fac_aux` such that `fermat_fac_aux n a` is the Fermat factorisation
of `n`, starting at `a`. That is, if `n < a`, we return `n`. Otherwise, we test if `bs : =a ^ 2 - n`
is a perfect square. If `bs` is a perfect square, return `a + sqrt bs`. Otherwise, increment `a`
by `1` and continue the process.
-/

open nat

def fermat_fac_aux (n : ℕ) : ℕ → ℕ | a :=
if h : n < a then n else
let bs := a * a - n  in
if (sqrt bs)^2 = bs then a + sqrt bs else
  have n - a < n + 1 - a, by
  { rw nat.sub_lt_sub_right_iff, exact lt_add_one _, exact le_of_not_gt h, },
  fermat_fac_aux (a + 1)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ k, n + 1 - k)⟩]}

/--
`fermat_fac n` is the result of applying Fermat factorisation to `n`.
-/
def fermat_fac (n : ℕ) := let c := sqrt n in
  if c^2 = n then c else fermat_fac_aux n (c + 1)

/-!
If the code below is uncommented, it spits out `3181`, a factor of 9539819.
-/
-- #eval fermat_fac 9539819

/--
`sqrt_tac` is used to prove `sqrt n = u`.
-/
meta def sqrt_tac := `[ symmetry, rw nat.eq_sqrt, norm_num ]

example : fermat_fac 9539819 = 3181 :=
begin
  rw fermat_fac, dsimp,
  rw [show sqrt 9539819 = 3088, by sqrt_tac, fermat_fac_aux], norm_num,
  have foo : ¬ (sqrt 2102 ^ 2 = 2102) := λ h,
    by { rw show sqrt 2102 = 45, by sqrt_tac at h, norm_num at h },
  simp only [foo, if_false], clear foo, rw fermat_fac_aux, rw [if_neg], dsimp, rw [if_pos],
  any_goals { norm_num, try { rw show sqrt 8281 = 91, by sqrt_tac, norm_num }, },
end

lemma fermat_fac_aux_dvd (n : ℕ) : ∀ (a : ℕ), a * a ≥ n → fermat_fac_aux n a ∣ n
| a := if h : n < a then by { rw fermat_fac_aux, simp [h] } else
if hsq : (sqrt (a * a - n))^2 = a * a - n then 
by { rw fermat_fac_aux, simp [h, hsq],
  intro hge,
  use a - sqrt (a * a - n),
  rw [←nat.sq_sub_sq, hsq, pow_two, nat.sub_sub_self hge] }
 else  have n - a < n + 1 - a, by
  { rw nat.sub_lt_sub_right_iff, exact lt_add_one _, exact le_of_not_gt h, },
 by { intro hge, rw fermat_fac_aux, simp [h, hsq], apply fermat_fac_aux_dvd, linarith }
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ k, n + 1 - k)⟩]}

/--
`fermat_fac n` divides `n`, for every `n`.
-/
lemma fermat_fac_dvd (n : ℕ) : fermat_fac n ∣ n :=
begin
  rw fermat_fac,
  by_cases h : (sqrt n) ^ 2 = n,
  { simp [h], use sqrt n, rw pow_two at h, rw h, },
  { simp [h], apply fermat_fac_aux_dvd, linarith [succ_le_succ_sqrt n], },
end

end fermat_factorisation

section using_well_founded_commmand

/-!
## The `using_well_founded` command

The argument for `using_well_founded`, a term of structure type `well_founded_tactics` is described
in `init.meta.well_founded_tactics`.

This structure has two fields: `dec_tac` and `rel_tac`. We've seen `rel_tac` already. It's purpose
is to create a well-founded relation (more precisely, to synthesize a term of type
`has_well_founded α`, where `α` is the type over which we are recursing).

The `dec_tac` field is used to synthesize a proof that the recursive application is decreasing.
-/

/--
`lg_using` is a redefinition of the function `lg` that employs `using_well_founded` to prove the
recursive application is decreasing.
-/
def lg_using : ℕ → ℕ
| 0 := 0
| (x + 1) := 1 + lg_using ((x + 1)/2)
  using_well_founded { dec_tac := `[exact nat.div_lt_self' _ _] }

def lg2_iv : ℕ → ℕ
| n := if h : n ≤ 1 then 0 else 1 + lg2_iv (n / 2)
using_well_founded
{ dec_tac := `[exact nat.div_lt_self (by linarith) (nat.le_refl 2)] }

end using_well_founded_commmand

section quick_sort

/-!
## Quick sort

We define `qsort`, the quick sort algorithm and prove that it sorts a list.

Might want to rewrite this using the definition given in core Lean `data.list.qsort`.
The definition there uses the notion of `partition`.

Note that mathlib has a defintion of `sorted` that is different from mine. It's in
`data.list.sort`.

A good discussion of quick sort proof is available at:
http://www.doc.ic.ac.uk/~scd/Dafny_Material/Lectures.pdf.
-/

open list

def at_most_list (x : ℕ) (xs : list ℕ) : list ℕ :=
  list.filter (λ y, y ≤ x) xs

def greater_list (x : ℕ) (xs : list ℕ) : list ℕ :=
  list.filter (λ y, x < y) xs

lemma filter_length_lt {p : ℕ → Prop} [decidable_pred p] :
  ∀ ys, (list.filter p ys).length < ys.length + 1
| [] := by simp
| (y :: ys) :=
begin
  simp only [list.filter, list.length],
  by_cases h : p y,
  { rw if_pos h, simp only [list.length, add_lt_add_iff_right], tauto, },
  { rw if_neg h, apply nat.lt.step, tauto, }
end

/-!
Lean can aid you in determining the correct inequality for well-founded recursion. Simply
write a proof *without* indicating the decreasing application and Lean will provide a helpful
error message, suggesting which inequality you must prove.
-/

/--
`qsort xs` returns a list `ys` such that `sorted ys` and `xs ~ ys`.
-/
def qsort : list ℕ → list ℕ
| [] := []
| (x :: xs) :=
  qsort (at_most_list x xs) ++ (x :: qsort (greater_list x xs))
  using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ ys, ys.length)⟩],
    dec_tac := `[exact filter_length_lt _] }

inductive sorted : list ℕ → Prop
| nil_sort : sorted []
| singleton_sort {x : ℕ} : sorted [x]
| cons_cons_sort {x y : ℕ} {xs : list ℕ} : x ≤ y → sorted (y :: xs) → sorted (x :: y :: xs)

open sorted

lemma sorted_cons {x : ℕ} {as : list ℕ} (has : sorted as) (h : ∀ a ∈ as, x ≤ a) : sorted (x :: as) :=
begin
  cases has with a' p q qs hpq hqs,
  { exact singleton_sort, },
  { simp at h, apply cons_cons_sort; assumption, },
  { apply cons_cons_sort _ has, apply h, simp, },
end

lemma le_of_sorted_cons {x : ℕ} {as : list ℕ} (h : sorted (x :: as)) : ∀ a ∈ as, x ≤ a :=
begin
  intros a has,
  induction' h with _ _ p ps hxp hps,
  { tauto, },
  { apply le_trans hxp, rw list.mem_cons_iff at has, 
    cases has,
    { subst has, },
    { exact ih _ has, }, },
end

lemma qsort_sorted_aux {x : ℕ} {as bs : list ℕ} (has : sorted as) (hbs : sorted bs) 
(hale : ∀ a ∈ as, a ≤ x) (hble : ∀ b ∈ bs, x ≤ b) : sorted (as ++ (x :: bs)) :=
begin
  induction as with q qs ih,
  { rw list.nil_append, exact sorted_cons hbs hble, },
  { cases has with _ _ r rs hqr hrs,
    { simp, apply sorted_cons,
      { simp at ih, apply ih, exact nil_sort, },
      { intros a hain, simp at hain, simp at hale,
        cases hain,
        { subst hain, exact hale, },
        { specialize hble _ hain, exact le_trans hale hble, }, }, },
    { apply sorted_cons,
      { apply ih hrs, intros a ha, simp at ha,
        cases ha,
        { subst ha, apply hale, simp, },
        { apply hale, right, right, exact ha, }, },
      { simp only [forall_eq_or_imp, list.append, list.mem_cons_iff],      
        rw and_iff_right hqr, clear ih,
        intros a hain,
        change (a ∈ rs ++ (x :: bs)) at hain, rw list.mem_append at hain,
        rcases hain with hain | rfl | hain,
        { apply le_trans hqr, apply le_of_sorted_cons hrs, exact hain,  },
        { apply hale, simp, },
        { specialize hble _ hain, apply le_trans _ hble, apply hale, simp, }, }, }, },
end

lemma perm_append_cons {xs as as' bs bs' : list ℕ} {y : ℕ}
(h : xs ~ y :: as ++ bs) (has : as ~ as') (hbs : bs ~ bs') : xs ~ as' ++ y :: bs' :=
calc xs ~ y :: as ++ bs : h
    ... ~ as ++ y :: bs : perm_middle.symm
    ... ~ as' ++ y :: bs : perm.append_right _ has 
    ... ~ as' ++ y :: bs' : perm.append_left as' (perm.cons _ hbs)

lemma perm_at_most_append_greater {x : ℕ} : ∀ as, as ~ (at_most_list x as) ++ (greater_list x as)
| [] := by { dsimp [at_most_list, greater_list], refl, }
| (a :: as) :=
begin
  have h := perm_at_most_append_greater as, dsimp [at_most_list, greater_list],
  by_cases ha : a ≤ x,
  { rw filter_cons_of_pos, swap, exact ha,
    rw filter_cons_of_neg, swap, linarith, apply perm.cons, exact h, },
  { rw filter_cons_of_neg, swap, exact ha, 
    rw filter_cons_of_pos, swap, linarith,
    exact perm.trans (perm.cons a h) perm_middle.symm, },
end

lemma qsort_sorted : ∀ xs, sorted (qsort xs) ∧ xs ~ qsort xs
| [] := by { simp [nil_sort, qsort], }
| (y :: ys) :=
begin
  rw qsort,  
  have h₁ := qsort_sorted (at_most_list y ys),
  have h₂ := qsort_sorted (greater_list y ys),
  split,
  { refine qsort_sorted_aux h₁.1 h₂.1 _ _,
    { intros a ha, 
      rw perm.mem_iff h₁.2.symm at ha, dsimp [at_most_list] at ha, simp at ha, exact ha.2, },
    { intros b hb,
      rw perm.mem_iff h₂.2.symm at hb, dsimp [greater_list] at hb, simp at hb, linarith, }, },
  { exact perm_append_cons (perm.cons y (perm_at_most_append_greater _)) h₁.2 h₂.2, },
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ ys, ys.length)⟩],
  dec_tac := `[exact filter_length_lt _] }

end quick_sort

end wf_exlean

end exlean