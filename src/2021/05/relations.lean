import tactic

@[derive decidable_rel]
def near_to (x y : ℕ) : Prop := (x - y) < 5 ∧ (y - x) < 5

local infix `∼`:50 := near_to

example : 5 ∼ 7 := by { split; norm_num }

example : reflexive near_to :=
by { intro x, split; { rw nat.sub_self, dec_trivial } }

example : symmetric near_to := λ x y ⟨hl, hr⟩, ⟨hr, hl⟩

example : ¬(transitive near_to) :=
begin
  intros h,
  apply (show ¬(20 ∼ 28), from dec_trivial),
  apply h (show 20 ∼ 24, from dec_trivial) (show 24 ∼ 28, from dec_trivial),
end