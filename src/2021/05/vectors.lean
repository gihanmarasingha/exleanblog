import data.vector data.real.basic

def double (n : ℕ) : ℤ := 2 * n

example : ℕ → ℤ := double

example : Π (n : ℕ), ℤ := double

def zero_list (n : ℕ) : list ℝ := list.repeat 0 n

example : zero_list 5 = [0,0,0,0,0] := rfl

def myvec : vector ℝ 5 := ⟨[5,10,15,20,25], rfl⟩

example : list ℝ := zero_list 100000

-- The line below doesn't work as `n` is arbitrary.
--example (n : ℕ) : vector ℝ n := ⟨zero_list n, rfl⟩

def zero_vec (n : ℕ) : vector ℝ n := ⟨zero_list n, list.length_repeat 0 n⟩

example : Π (m : ℕ), vector ℝ m := zero_vec

namespace extras

def myvec' : vector ℕ 5 :=
{ val := [5,10,15,20,25],
  property := rfl }

def two : fin 5 := ⟨2, dec_trivial⟩

-- #reduce vector.nth myvec' 2

def zero_list' : ℕ → list ℝ
| 0       := []
| (n+1)   := 0 :: (zero_list' n)

def zero_list'' : ℕ → list ℝ := λ n, nat.rec_on n [] (λ n t, 0 :: t)

example (n : ℕ) : zero_list n = zero_list'' n :=
begin
  induction n,
  { refl },
  { simpa [zero_list, zero_list''] }
end

example (xs : list ℝ) : ∃ n : ℕ, list.length xs = n :=
begin
  induction xs with x xs h,
  { use 0, simp },
  { cases h with n h, 
    use (n+1), simp [h], }
end

lemma length_zero_list' : ∀ n, list.length (zero_list' n) = n
| 0     := rfl
| (n+1) := by { simp only [list.length, zero_list', length_zero_list'] }

universe u

def const_vec (c : ℝ) (n : ℕ) : vector ℝ n := ⟨list.repeat c n, list.length_repeat c n⟩

def const_vec' {α} (c : α) (n : ℕ) : vector α n := ⟨list.repeat c n, list.length_repeat c n⟩

open list

def add_vec : Π {n : ℕ} (v₁ v₂ : vector ℕ n), vector ℕ n
| 0       _              _             := ⟨[],rfl⟩
| (n+1)   ⟨x :: v₁, p₁⟩  ⟨y :: v₂, p₂⟩  :=
(x + y) ::ᵥ (@add_vec n ⟨v₁, nat.succ.inj p₁⟩ ⟨v₂, nat.succ.inj p₂ ⟩)

example : add_vec  ⟨[0,1,2],rfl⟩ ⟨[5,6,7],rfl⟩ = ⟨[5,7,9], rfl⟩ := rfl

lemma nth_add_nth : Π {n : ℕ} (v₁ v₂ : vector ℕ n) (a : fin n), v₁.nth a + v₂.nth a = (add_vec v₁ v₂).nth a
| 0 _ _ ⟨a, p⟩ := absurd p (nat.not_lt_zero a)
| (n+1) ⟨x :: v₁, p₁⟩ ⟨y :: v₂, p₂⟩ ⟨0, h⟩ := by { simp only [vector.nth, add_vec, fin.mk_zero, fin.val_zero', vector.nth_cons_zero, nth_le], }
| (n+1) ⟨x :: v₁, p₁⟩ ⟨y :: v₂, p₂⟩ ⟨a+1,h⟩ :=
begin
  have ha : (⟨a+1,h⟩ : fin (n+1)) = fin.succ (⟨a, nat.succ_lt_succ_iff.mp h⟩), from rfl,
  rw [ha, add_vec, vector.nth_cons_succ, ←@nth_add_nth n],
  have h₁ : (⟨x :: v₁, p₁⟩ : vector ℕ (n+1)) = x ::ᵥ ⟨v₁, nat.succ.inj p₁⟩, { rw vector.cons, refl, },
  have h₂ : (⟨y :: v₂, p₂⟩ : vector ℕ (n+1)) = y ::ᵥ ⟨v₂, nat.succ.inj p₂⟩, { rw vector.cons, refl, },
  rw [h₁, h₂, vector.nth_cons_succ, vector.nth_cons_succ]
end

end extras

namespace generalisation

open list

variables {α : Type*} [has_add α]

def add_vec : Π {n : ℕ} (v₁ v₂ : vector α n), vector α n
| 0       _              _             := ⟨[],rfl⟩
| (n+1)   ⟨x :: v₁, p₁⟩  ⟨y :: v₂, p₂⟩  :=
(x + y) ::ᵥ (@add_vec n ⟨v₁, nat.succ.inj p₁⟩ ⟨v₂, nat.succ.inj p₂ ⟩)

lemma nth_add_nth : Π {n : ℕ} (v₁ v₂ : vector α n) (a : fin n), v₁.nth a + v₂.nth a = (add_vec v₁ v₂).nth a
| 0 _ _ ⟨a, p⟩ := absurd p (nat.not_lt_zero a)
| (n+1) ⟨x :: v₁, p₁⟩ ⟨y :: v₂, p₂⟩ ⟨0, h⟩ := by { simp [vector.nth, add_vec], }
| (n+1) ⟨x :: v₁, p₁⟩ ⟨y :: v₂, p₂⟩ ⟨a+1,h⟩ :=
begin
  have ha : (⟨a+1,h⟩ : fin (n+1)) = fin.succ (⟨a, nat.lt_of_succ_lt_succ h⟩), from rfl,
  rw [ha, add_vec, vector.nth_cons_succ, ←@nth_add_nth n],
  have h₁ : (⟨x :: v₁, p₁⟩ : vector α (n+1)) = x ::ᵥ ⟨v₁, nat.succ.inj p₁⟩, { rw vector.cons, refl, },
  have h₂ : (⟨y :: v₂, p₂⟩ : vector α (n+1)) = y ::ᵥ ⟨v₂, nat.succ.inj p₂⟩, { rw vector.cons, refl, },
  rw [h₁, h₂, vector.nth_cons_succ, vector.nth_cons_succ]
end

end generalisation