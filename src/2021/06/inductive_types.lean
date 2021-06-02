import tactic

namespace exlean

inductive foob
| red : foob
| blue (n : nat) : foob
| green (a : ℕ) (b : ℤ) : foob → foob → foob

section inductive_propositions

/-
The following defintions `myor` and `myand` are quite different from the definitions `and` and `or`.
In particular, for each `α β : Prop`, `myand α β : Type`, whereas `and α β : Prop`.
-/
inductive myor (α β : Prop)
| inl (h : α) : myor
| inr (h : β) : myor

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

inductive le (a : ℕ) : ℕ → Prop
| refl : le a
| step : ∀ {b}, le b → le (succ b)

inductive le' : ℕ → ℕ → Prop
| refl : ∀ (a : ℕ), le' a a
| step : ∀ (a b : ℕ), le' a b → le' a (succ b)

example : le 5 5 := le.refl

example : le' 5 5 := le'.refl 5

local infix ` ≤ ` := le

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

end Tree

end trees

end exlean