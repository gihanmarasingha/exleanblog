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

section extras

def myvec' : vector ℕ 5 :=
{ val := [5,10,15,20,25],
  property := rfl }

def two : fin 5 := ⟨2, dec_trivial⟩

#reduce vector.nth myvec' 2

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

#check const_vec

def const_vec' {α} (c : α) (n : ℕ) : vector α n := ⟨list.repeat c n, list.length_repeat c n⟩

#check @const_vec

open list

-- Rewrite the function below using vector cons `::ᵥ`.
/- def add_vec' {n : ℕ} (v₁ v₂ : vector ℕ n) : vector ℕ n :=
begin
  induction n with n hn,
  { exact ⟨[],rfl⟩ },
  { rcases v₁ with ⟨_ | ⟨x, xs⟩, p₁⟩,
    { simp only [length] at p₁, contradiction },
    rcases v₂ with ⟨_ | ⟨y, ys⟩, p₂⟩,
    { simp only [length] at p₂, contradiction },
    have h₁ : length xs = n, { simp [length] at p₁, exact p₁, },
    have h₂ : length ys = n, { simp [length] at p₂, exact p₂, },
    cases hn ⟨xs, h₁⟩ ⟨ys, h₂⟩ with v₃ p₃,
    exact ⟨(x+y) :: v₃, by { rw ←p₃, simp }⟩ },
end -/

def add_vec : Π {n : ℕ} (v₁ v₂ : vector ℕ n), vector ℕ n
| 0       _              _             := ⟨[],rfl⟩
| (n+1)   ⟨x :: v₁, p₁⟩  ⟨y :: v₂, p₂⟩  :=
(x + y) ::ᵥ (@add_vec n ⟨v₁, by { simp [length] at p₁, exact p₁} ⟩ ⟨v₂, by {simp [length] at p₂, exact p₂} ⟩)

/- lemma boo {n : ℕ} (v₁ v₂ : vector ℕ n) (x y : ℕ) (a : fin n) :
(add_vec (x ::ᵥ v₁) (y ::ᵥ v₂)).nth abs_le_abs = 
 -/
example : add_vec  ⟨[0,1,2],rfl⟩ ⟨[5,6,7],rfl⟩ = ⟨[5,7,9], rfl⟩ := rfl

/- example {n : ℕ} (v₁ v₂ : vector ℕ n) (a : fin n) : v₁.nth a + v₂.nth a = (add_vec v₁ v₂).nth a :=
begin
  induction n with n hn,
  { cases a, linarith, },
  { sorry }
end  -/

end extras