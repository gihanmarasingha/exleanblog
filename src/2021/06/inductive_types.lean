import tactic tactic.induction

namespace exlean

inductive fuzzy
  | yes : fuzzy
  | no : fuzzy
  | meh : fuzzy

example : Type := fuzzy

open fuzzy

namespace fuzzy

universe u

def fuzzy.rec_on' {C : fuzzy → Sort u} (t : fuzzy) (h₀ : C yes) (h₁ : C no) (h₂ : C meh) : C t :=
  fuzzy.rec_on t h₀ h₁ h₂

example : fuzzy := yes

def tea (t : fuzzy) : string :=
fuzzy.rec_on t "Here's your tea!" "Get out." "Are you sure?"

example : tea yes = "Here's your tea!" := rfl

def tea2 (t : fuzzy) : string :=
@fuzzy.rec_on (λ x, string) t "Here's your tea!" "Get out." "Are you sure?"

def tea3 (t : fuzzy) : string :=
begin
  cases t,
  { exact "Here's your tea!" },
  { exact "Get out." },
  { exact "Are you sure?"}
end

def tea4 : fuzzy → string
  | yes := "Here's your tea!"
  | no  := "Get out."
  | meh := "Are you sure?"

def tea5 (f : fuzzy) : string :=
"My response to your response is: '" ++
match f with
  | yes := "Here's your tea!"
  | no  := "Get out."
  | meh := "Are you sure?"
end
++ "' "

#eval tea5 yes

lemma only_ynm (t : fuzzy) : t = yes ∨ t = no ∨ t = meh :=
fuzzy.rec_on t (or.inl rfl) (or.inr $ or.inl rfl) (or.inr $ or.inr rfl)

def C_only_ynm := λ (x : fuzzy), x = yes ∨ x = no ∨ x = meh

lemma only_ynm2 (t : fuzzy) : t = yes ∨ (t = no ∨ t = meh) :=
@fuzzy.rec_on C_only_ynm t (or.inl rfl) (or.inr $ or.inl rfl) (or.inr $ or.inr rfl)

lemma only_ynm3 (t : fuzzy) : t = yes ∨ t = no ∨ t = meh :=
begin
  apply fuzzy.rec_on t,
  { left, refl, },
  { right, left, refl, },
  { right, right, refl, },
end

lemma only_ynm4 (t : fuzzy) : t = yes ∨ t = no ∨ t = meh :=
begin
  cases t,
  { left, refl, },
  { right, left, refl, },
  { right, right, refl, },
end

lemma only_ynm5 (t : fuzzy) : t = yes ∨ t = no ∨ t = meh := by { cases t; tauto }

def yes_no : ¬ yes = no .

def yes_no2 : ¬ yes = no := assume h : yes = no, fuzzy.no_confusion h

def yes_no3 : ¬ yes = no := assume h : yes = no, @fuzzy.no_confusion false yes no h

def f_no_confusion_type_full : Sort u → fuzzy → fuzzy → Sort u :=
λ (P : Sort u) (v₁ v₂ : fuzzy),
  @fuzzy.rec_on (λ (v₁ : fuzzy), Sort u) v₁
    (@fuzzy.rec_on (λ (v₁ : fuzzy), Sort u) v₂ (P → P) P P)
    (@fuzzy.rec_on (λ (v₁ : fuzzy), Sort u) v₂ P (P → P) P)
    (@fuzzy.rec_on (λ (v₁ : fuzzy), Sort u) v₂ P P (P → P))

def f_no_confusion_type : Sort u → fuzzy → fuzzy → Sort u :=
λ (P : Sort u) (v₁ v₂ : fuzzy),
  fuzzy.rec_on v₁
    (fuzzy.rec_on v₂ (P → P) P P)
    (fuzzy.rec_on v₂ P (P → P) P)
    (fuzzy.rec_on v₂ P P (P → P))

def f_no_confusion : Π {P : Sort u} {v₁ v₂ : fuzzy}, v₁ = v₂ → f_no_confusion_type P v₁ v₂ :=
λ {P : Sort u} {v₁ v₂ : fuzzy} (h : v₁ = v₂),
  eq.rec_on h (λ (h₂ : v₁ = v₁), fuzzy.rec_on v₁ (λ (a : P), a) (λ (a : P), a) (λ (a : P), a)) h

end fuzzy

namespace staff

inductive staff
  | hod : staff
  | doctor (n : fuzzy) : staff
  | secretary (id : ℕ) (boss : staff) : staff

example : Type := staff

open staff fuzzy

def jill : staff := hod

def dr_no : staff := doctor no

def dr_meh : staff := doctor meh

def justin : staff := secretary 10 jill

def selima : staff := secretary 5 dr_no

def gursel : staff := secretary 7 selima

def salary : staff → ℚ
  | hod := 500000
  | (doctor yes) := 100000
  | (doctor _) := 5000
  | (secretary num boss) := 1 / num + (salary boss) / 2

example : salary dr_meh = 5000 := rfl

example : salary selima = 12501 / 5 := by { dsimp [selima, dr_no, salary], norm_num }

def salary2 (s : staff) : ℚ := staff.rec_on s
  500000 (λ (f : fuzzy), f.rec_on 100000 5000 5000)
  (λ (n : ℕ) (boss : staff) (bs : ℚ), 1 / n + bs / 2)

def salary3 (s : staff) : ℚ := staff.rec_on s
  500000 (λ f, f.rec_on 100000 5000 5000)
  (λ n _ bs, 1 / n + bs / 2)

def salary_new : staff → ℚ
  | hod := 500000
  | (doctor yes) := 100000
  | (doctor _) := 5000
  | (secretary 0 boss) := (salary_new boss) / 200
  | (secretary (n+1) boss) := 1 / n + salary_new (secretary n boss)

end staff

section inductive_propositions

/-
The following defintions `myor` and `myand` are quite different from the definitions `and` and `or`.
In particular, for each `α β : Prop`, `myand α β : Type`, whereas `and α β : Prop`.
-/

-- `myor` and `myand` ARE NOT INDUCTIVELY-DEFINED PROPOSITIONS!!!
inductive myor (α β : Prop)
  | inl (h : α) : myor
  | inr (h : β) : myor

example : Prop → Prop → Type := myor

inductive myand (α β : Prop)
  | intro (left : α) (right : β) : myand

/-
Some proofs work as expected.
-/
example (p q : Prop) : myand p q → p :=
begin
  intro h,
  cases h with hp hq,
  exact hp,
end

example (p q : Prop) : myand p q → myand q p :=
begin
  intro h,
  cases h with hp hq,
  split,
  { exact hq, },
  { exact hp, },
end

/-
However, the following statement does not type check. The issue is that `myand q r : Type`, 
but `myand q r` is the second argument to `myand` in `myand p (myand q r)`. Both arguments of
`myand` are required to have type `Prop`.
-/
--example (p q r : Prop) : myand p (myand q r) → q := sorry

/-
One major difference between `Prop` and other type universes is that an inductive type in `Prop`
can only eliminate to other types in `Prop`. Put another way, if `α` is an inductive type in `Prop`
then the motive `C` of `α.rec_on` is also of type `Prop`.
-/

-- Here's a pukka application of `or.rec_on`.
example (p q : Prop) (h : or p q) : or q p := or.rec_on h (λ hp, or.inr hp) (λ hq, or.inl hq)

-- The following doesn't work.
-- example (p q : Prop) (h : or p q) : ℕ := or.rec_on h (λ hp, 5) (λ hq, 10)

-- But it does work with `myor` as `myor` is not a type in `Prop`.
example (p q : Prop) (h : myor p q) : ℕ := myor.rec_on h (λ hp, 5) (λ hq, 10)

example (p q : Prop) (h : and p q) : ℕ  := and.rec_on h (λ hp hq, 5)

end inductive_propositions

section less_than_or_equal

open nat

/-!
We look at two defintions of `le`. The first is the standard defintion found in Lean. With this
definition, `le` is a family of inductive types.
-/
inductive le (a : ℕ) : ℕ → Prop
  | refl : le a
  | step : ∀ {b}, le b → le (succ b)

/-!
The definition above leads to an elimination principle. Suppose we have `h : x ≤ y` and we want
to prove `P y`, for some predicate `P`. We can do this by considering separately the two possible
ways in which `h` could have been constructed.

1. `h` could be the result of `refl`. In which case, `y` is `x` and we have to prove `P x`.
2. `h` could be the result of `step`. Then there is some `t` for which `y` is `succ t` and we know
`x ≤ t`. Thus, we need to prove for every `t : ℕ`, given `x ≤ t`, given `P t`, we have `P (succ t)`.
-/

/-!
Here's another definition `le'`.
-/
inductive le' : ℕ → ℕ → Prop
  | refl : ∀ (a : ℕ), le' a a
  | step : ∀ (a b : ℕ), le' a b → le' a (succ b)

example : le 5 5 := le.refl

example : le' 5 5 := le'.refl 5

local infix ` ≤ ` := le

#check @le.rec_on

#check eq.refl

#check @list.cons

example (a b c : ℕ) (hab : le a b) (hbc : le b c) : le a c := le.rec_on hbc hab
  (λ d hbd had, by { apply le.step, exact had})

/-
It took me ages to figure out the simple proof below. This is because I was trying induction on
`hab` rather than `hbc`.
-/
lemma le_trans (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
begin
  induction hbc with d hbd had,
  { exact hab, },
  { apply le.step, exact had, }
end

lemma le_rec (x : ℕ) (C : ℕ → Prop) (h1 : C x) (h2 : (∀ (y : ℕ), x ≤ y → C y → C y.succ)) :
 ∀ {n : ℕ}, x ≤ n → C n := λ n, (le.rec h1) h2

lemma le_rec' (x n : ℕ) (C : ℕ → Prop)
(h1 : C x) (h2 : (∀ (y : ℕ), x ≤ y → C y → C y.succ)) (h3 : x ≤ n) : C n :=
 (λ n, (le.rec h1) h2) n h3

lemma le_trans' (a b c : ℕ) : a ≤ b → b ≤ c → a ≤ c :=
begin
  let C := λ m, a ≤ m,
  intro hab,
  have h2 : ∀ (y : ℕ), b ≤ y → C y → C y.succ,
  { intros y hby hay,
    apply le.step,
    exact hay, },
  apply le_rec b C hab h2,
end

lemma le_trans'' (a b c : ℕ) : a ≤ b → b ≤ c → a ≤ c :=
begin
  let C := λ m, a ≤ m,
  intros h1 h3,
  have h2 : ∀ (y : ℕ), b ≤ y → C y → C y.succ,
  { intros y hby hay,
    apply le.step,
    exact hay, },
  exact le_rec' b c C h1 h2 h3,
end

end less_than_or_equal

section trees

inductive Tree
  | empty : Tree
  | node  : ℕ → Tree → Tree → Tree

open Tree

example : Tree := empty

def smalltree : Tree := node 3 (node 5 (node 7 empty empty) empty) (node 6 empty (node 2 empty empty))

namespace Tree

def sum (t : Tree) : ℕ :=
begin
  refine Tree.rec_on t 0 _,
  intros n ltree rtree ltree_sum rtree_sum,
  exact ltree_sum + n + rtree_sum, 
end

lemma sum_empty : sum empty = 0 := rfl

lemma sum_node (n : ℕ) (lt rt : Tree) : sum (node n lt rt) = (sum lt) + n + (sum rt) := rfl

def left_combine (t s : Tree) : Tree :=
begin
  refine Tree.rec_on t s _,
  intros n lt rt ilt irt,
  exact node n ilt rt
end

lemma left_combine_empty (s : Tree) : left_combine empty s = s := rfl

lemma left_combine_node (n : ℕ) (lt rt s : Tree) :
left_combine (node n lt rt) s = node n (left_combine lt s) rt := rfl

def mytree : Tree := node 10 (node 50 empty empty) (node 20 (node 30 empty empty) empty)

lemma sum_add (t s : Tree) : sum (left_combine t s) = (sum t) + (sum s) :=
begin
  refine Tree.rec_on t _ _,
  { rw [sum_empty, left_combine_empty, zero_add], },
  { intros n lt rt ilt irt, simp only [sum_node, left_combine_node, ilt], linarith, }
end

inductive sorted_tree : Tree → Prop
  | srt_empty : sorted_tree empty
  | srt_neither {n : ℕ} : sorted_tree (node n empty empty)
  | srt_left {n m : ℕ} {lt rt : Tree} : m ≤ n → sorted_tree (node m lt rt)
    → sorted_tree (node n (node m lt rt) empty)
  | srt_right {n m : ℕ} {lt rt : Tree} : n ≤ m → sorted_tree (node m lt rt)
    → sorted_tree (node n empty (node m lt rt))
  | srt_both {n m p : ℕ} {ltm rtm ltp rtp : Tree} : m ≤ n → n ≤ p → sorted_tree (node m ltm rtm)
    → sorted_tree (node p ltp rtp) → sorted_tree (node n (node m ltm rtm) (node p ltp rtp))

open sorted_tree

example : sorted_tree (node 10 empty (node 20 empty empty)) :=
begin
  refine srt_right dec_trivial _,
  exact srt_neither,
end

def tree1 := node 10 (node 5 empty empty) (node 30 empty empty)

lemma test_srt1 : sorted_tree tree1 :=
by { refine srt_both dec_trivial dec_trivial _ _; exact srt_neither }

def tree2 := node 20 tree1 empty

lemma test_srt2 : sorted_tree tree2 :=
begin
  dsimp [tree2,tree1],
  refine srt_left dec_trivial _,
  exact test_srt1,
end

def tree_insert : ℕ → Tree → Tree
  | x empty := node x empty empty
  | x (node a left right) := if x = a then node a left right else
      if x <= a then node a (tree_insert x left) right else node a left (tree_insert x right)

def list_to_tree : list ℕ → Tree := list.foldr tree_insert empty

example : list_to_tree [1,2,3] = node 3 (node 2 (node 1 empty empty) empty) empty := rfl

def tree1' := list_to_tree [30,5,10]

example : tree1 = tree1' := rfl

def tree2' := list_to_tree [30,10,5,20]

#reduce tree2'

example (xs : list ℕ) (x : ℕ) : ∃ l r, list_to_tree (xs ++ [x]) = node x l r :=
begin
  induction xs with y ys ih,
  { use [empty, empty], refl, },
  { unfold list_to_tree at *, dsimp,
    rcases ih with ⟨l1, r1, ih⟩,
    rw ih,
    cases (lt_trichotomy x y) with h h,
    { use [l1, tree_insert y r1],
      dsimp [tree_insert],
      rw if_neg,
      { rw if_neg,
        { intro hle, apply lt_irrefl x, apply lt_of_lt_of_le h hle, }, },
      { intro heq, rw heq at h, exact (lt_irrefl x) h, }, },
    { cases h with h h,
      { use [l1, r1], dsimp [tree_insert], rw if_pos, symmetry, assumption, },
      use [tree_insert y l1, r1], 
      dsimp [tree_insert],
      rw if_neg,
      { rw if_pos,
        { exact le_of_lt h }, },
      { intro heq, rw heq at h, exact (lt_irrefl x) h, }, }, }
end

/- lemma sorted_of_list (t : Tree) (h : sorted_tree t) : ∃ xs, t = list_to_tree xs :=
begin
  induction h,
  { use ([] : list ℕ), refl, },
  case srt_neither : x { use ([x] : list ℕ), refl, },
  case srt_left : n m l r hle hsrt ih
  { cases ih with xs ih,
    use (xs ++ [m]),
    dsimp [list_to_tree],
    rw [ih, list.foldr_append],

   },
  {   },
  {   },
end -/

end Tree

end trees

end exlean