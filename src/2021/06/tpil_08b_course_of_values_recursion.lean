import tactic

/-
In this file, we'll focus on functions of a natural number variable. The ideas generalise to other
inductive types.
-/

namespace primitive_recursion

  /-
  Our aim is to define, recursively, a function `pow2 : ℕ → ℕ` so that `pow2 n = 2^n`.
  We assume given an operation on multiplication.

  As `ℕ` has two constructors, `zero : ℕ` and `succ : ℕ → ℕ`, it suffices to define `pow2 zero`
  and `pow2 (succ n)`, given `n : ℕ`.

  A (primitive) rescursive definition of `pow2` will give `pow2 (succ n)` only in terms of 
  `pow2 n`.

  The equation compiler permits a striaghtfoward notation for this kind of definition.
  -/

  

  open nat

  def pow2 : ℕ → ℕ
  | zero      := 1
  | (succ n)  := 2 * (pow2 n)

  example : pow2 5 = 32 := rfl

  /-
  However, the compiler does not (immediately) produce a primitive recursive definition. Instead,
  it uses course-of-values recursion. We'll come to this later. For now, let's see a primitive
  recursive definition of the same.
  -/

  #check @nat.rec_on 

  def pow2' : ℕ → ℕ := λ n, @nat.rec_on (λ (z : ℕ), ℕ) n 1 (λ m hm, 2 * hm)

  example : pow2' 5 = 32 := rfl

  def boo : Π (n : ℕ), vector ℕ n :=
  λ n, nat.rec_on n ⟨[],dec_trivial⟩ (λ m hm, vector.cons m hm)

  #eval vector.to_list (boo 3)


  /-
  Primitive recursive functions of a natural number variable can be written using the Lean
  constant `nat.rec` (or variants such as `nat.rec_on` and `nat.cases_on`).
  -/

  open nat
 
  def fib_aux : ℕ → ℕ × ℕ
  | 0         := ⟨0,1⟩
  | (n+1)     := ⟨(fib_aux n).snd, (fib_aux n).fst + (fib_aux n).snd⟩

  def fib_aux' (n : ℕ) : ℕ × ℕ := nat.rec_on n ⟨0,1⟩ (λ m ⟨f1, f2⟩, ⟨f2, f1 + f2⟩)

  def fib_pr : ℕ → ℕ := λ n, (fib_aux n).fst
  def fib_pr' : ℕ → ℕ := λ n, (fib_aux' n).fst

  #eval fib_pr 7
  #eval fib_pr' 7

end primitive_recursion


namespace fibonacci

  -- The Fibonacci sequence.
  def fib : nat → nat
  | 0     := 1
  | 1     := 1
  | (n+2) := fib (n+1) + fib n

  example : fib 0 = 1 := rfl
  example : fib 1 = 1 := rfl
  example (n : nat) : fib (n + 2) = fib (n + 1) + fib n := rfl

  example : fib 7 = 21 := rfl
  example : fib 7 = 21 :=
  begin
    dsimp [fib],   -- expands fib 7 as a sum of 1's
    reflexivity
  end

  /-
  Above, we defined `fib (n+2)` not only in terms of `fib (n+1)` but also in terms of `fib n`.

  The equation compiler converts this not into a `nat.rec_on` definition, but into a defintion
  using `nat.brec_on`, this being an analogue of strong induction.
  -/

  /-
  As seen below, the `nat.brec_on` constant takes a motive `C : ℕ → Sort u`, a natural number `n`,
  and a (dependent) function `F : Π (m : ℕ), nat.below C m → C m`. It returns a term of type `C n`.
  -/
  universe u
  variable (C : ℕ → Sort u) -- A motive.
  example : Π (n : ℕ), (Π (m : ℕ), nat.below C m → C m) → C n := @nat.brec_on C

  example : ℕ → Sort (max 1 u) := nat.below C

  /-
  For a given `n : ℕ`, the type `nat.below C (succ n)` is a structure whose terms record
  elements of `C 0`, `C 1`, ... `C n`.

  In practice, we may want to define a (dependent) function `g : Π (n : ℕ), C n`. In the simple case
  where `C n = C m` for every `n m : ℕ`, we can write this as `g : ℕ → α`, denoting by `α` the
  constant value of `C n`.

  Let `n : ℕ`. Informally, suppose we have a 'function' `f` such that for every `m : ℕ`,
  `f(m)` maps `g(0), g(1), ... g(m-1)` to `g(m)`. Then we construct `g(n)` by applying
  `f(n)` to an already-constructed sequence of values `g(0), g(1), ..., g(n-1)`.

  `nat.brec_on` formalises this notion. We treat `F : Π (m : ℕ), nat.below C m → C m` as being the
  function that produces `g(m)` (where `g` is the function being defined) from `g(0), ... , g(m-1)`.

  In practice, the task is to understand *how* elements of type `nat.below C m` encode the
  values `g(0), ..., g(m-1)`.
  -/
  variable blog0 : nat.below C 0
  variable blog1 : nat.below C 1
  variable blog2 : nat.below C 2
  variable blog3 : nat.below C 3

  #check ( blog0 : punit )
  #check ( blog1 : pprod (pprod (C 0) punit) punit )
  #check ( blog2 : pprod (pprod (C 1) (pprod (pprod (C 0) punit) punit)) punit )
  #check ( blog3 : pprod (pprod (C 2) (pprod (pprod (C 1) (pprod (pprod (C 0) punit) punit)) punit)) punit )

  /-
  You might guess from this that if `nat.below C n = ih`, then 
  `nat.below C (succ n) = pprod (pprod (C n) ih) punit`.

  This expectation is borne out in the defintion of `nat.below`, as seen below. Note that this
  constant is created automatically by Lean.
  -/

  @[reducible]
  protected def nat.below : (ℕ → Sort u) → ℕ → Sort (max 1 u) :=
  λ (C : ℕ → Sort u) (n : ℕ),
    nat.rec punit (λ m ih, pprod (pprod (C m) ih) (punit : Sort (max 1 u))) n


  /-
  We *construct* terms of type `nat.below C' n` for various `n`, taking `C' := (λ (m : ℕ), ℕ)`.
  -/
  def C' := λ (m : ℕ), ℕ

  def plog0 : nat.below C' 0 := punit.star
  def plog1 : nat.below C' 1 := ⟨⟨(3 : ℕ), punit.star⟩, punit.star⟩
  def plog2 : nat.below C' 2 := ⟨⟨(4 : ℕ), ⟨⟨(3 : ℕ), punit.star⟩, punit.star⟩⟩ , punit.star⟩
  
  -- We extract data from these terms using `fst` and `snd`.
  example : plog2.fst.fst = (4 : nat) := rfl
  example : plog2.fst.snd.fst.fst = (3 : nat) := rfl


  /-
  The automatically-generated constant `nat.brec_on` has (pretty much) the following definition.
  -/
  @[reducible]
  protected def nat.brec_on : Π {C : ℕ → Sort u} (n : ℕ), (Π (m : ℕ), nat.below C m → C m) → C n :=
  λ {C : ℕ → Sort u} (n : ℕ) (F : Π (m : ℕ), nat.below C m → C m),
    pprod.fst (
      nat.rec_on n ⟨F 0 punit.star, punit.star⟩
      (λ (m : ℕ) (ih : pprod (C m) (nat.below C m)), ⟨F m.succ ⟨ih, punit.star⟩, ⟨ih, punit.star⟩⟩)
      : pprod (C n) (nat.below C n)  )

  /-
  In stages, we'll contruct the `fib` function manually. The innermost operation is to take
  `n₁ : ℕ` and `h₁ : nat.below C' (n₁ + 2)` and return `h₁.fst.fst + h₁.fst.snd.fst.fst`.

  We want to apply this to `a : ℕ` where `a = n₁ + 2`. We can't satisfy this for every `a : ℕ`
  (in particular, we can't do this for `a = 0` or `a = 1`). Instead, we'll have separate
  functions to deal with the base case and 'pass' the `nat.below C' a` structure down the
  levels of nested functions until we get to the innermost function.
  -/
  def inner₁ (n₁ : ℕ) (h₁ : nat.below (λ _ : ℕ, ℕ) (n₁ + 2)) := h₁.fst.fst + h₁.fst.snd.fst.fst

  def inner₂ (n₂ : ℕ) :=
    @nat.cases_on (λ m₂ : ℕ, nat.below C' (m₂ + 1) → ℕ) n₂ (λ _ : nat.below C' 1, 1) inner₁

  def inner₃ (n₃ : ℕ) (h₃ : nat.below C' (n₃ + 1)) := inner₂ n₃ h₃

  def inner₄ (n₄ : ℕ) :=
    @nat.cases_on (λ m₄ : ℕ, nat.below C' m₄ → ℕ) n₄ (λ _ : nat.below C' 0, 1) inner₃

  def inner₅ (n₅ : ℕ) (h₅ : nat.below C' n₅) := inner₄ n₅ h₅

  def fib' (a : ℕ) : ℕ := nat.brec_on a inner₅

  #eval list.map (λ n, fib' n - fib n) (list.range 10)

  def boo₁ (n₁ : ℕ) (h₁ : nat.below (λ _ : ℕ, ℕ) (n₁ + 1)) := 2* h₁.fst.fst

  def boo₂ (n₂ : ℕ) :=
    @nat.cases_on (λ m₂ : ℕ, nat.below C' m₂ → ℕ) n₂ (λ _ : nat.below C' 0, 1) boo₁

  def pow2 (a : ℕ) : ℕ := nat.brec_on a boo₂

  #check @nat.cases_on

  def pow2' (a : ℕ) : ℕ := nat.brec_on a
   (λ n₂, @nat.cases_on (λ m₂ : ℕ, nat.below C' m₂ → ℕ) n₂ (λ _ : nat.below C' 0, 1) boo₁)

  def pow2'' (a : ℕ) : ℕ  := nat.brec_on a
  ( λ n₂, @nat.cases_on (λ m₂ : ℕ, nat.below C' m₂ → ℕ) n₂ (λ _ : nat.below C' 0, 1) 
    ( λ n₁ h₁,  2* h₁.fst.fst) )

  
  #eval pow2 20
  #eval pow2' 20
  #eval pow2'' 20

  def fib'' (a : ℕ) : ℕ :=
    nat.brec_on a
    ( λ (n₁ : ℕ) (h₁ : nat.below C' n₁),
      ( λ (n₂ : ℕ) (h₂ : nat.below C' n₂),
        (@nat.cases_on (λ m₁ : ℕ, nat.below C' m₁ → ℕ) n₂
        (λ _ : nat.below C' 0, 1)
        ( λ (n₃ : ℕ) (h₃ : nat.below C' (nat.succ n₃)),
          (@nat.cases_on (λ m₂ : ℕ, nat.below C' (nat.succ m₂) → ℕ) n₃
          (λ _ : nat.below C' 1, 1)
          ( λ (n₄ : ℕ) (h₅ : nat.below C' (nat.succ (nat.succ n₄))),
            (h₅.fst.fst + h₅.fst.snd.fst.fst) ) ) h₃ ) ) h₂ ) n₁ h₁ )

end fibonacci

def append {α : Type*} : list α → list α → list α
| []     l := l
| (h::t) l := h :: append t l

namespace fib_vector

  /-
  We write a function `fib''` such that for every `a : ℕ`, `fib'' a` is a length `a+1` vector of
  natural numbers consisting of the Fibonacci numbers from `0` to `a`.
  -/
  def C' := λ (m : ℕ), vector ℕ (m+1)

  example : vector ℕ 1 := ⟨[1], dec_trivial⟩
  example : vector ℕ 2 := ⟨[1,1], dec_trivial⟩

  example :  vector.head (⟨[1,2], dec_trivial⟩ : vector ℕ 2) = 1 := dec_trivial 

  example : vector.head (vector.tail (⟨[1,2], dec_trivial⟩ : vector ℕ 2)) = 2 := dec_trivial 

  example (n₄ : ℕ) (h₅ : nat.below C' (n₄ + 2)) : C' (n₄ + 1) := h₅.fst.fst

  def moop (n : ℕ) (h : nat.below C' (n + 2)) : C' (n+2) :=
    let fvec := h.fst.fst in
    vector.cons (vector.head fvec + vector.head (vector.tail fvec)) fvec

  def fib'' (a : ℕ) : C' a :=
    nat.brec_on a
    ( λ (n₁ : ℕ) (h₁ : nat.below C' n₁),
      ( λ (n₂ : ℕ) (h₂ : nat.below C' n₂),
        (@nat.cases_on (λ m₁ : ℕ, nat.below C' m₁ → vector ℕ (m₁+1)) n₂
        (λ _ : nat.below C' 0, ⟨[1], dec_trivial⟩)
        ( λ (n₃ : ℕ) (h₃ : nat.below C' (n₃ + 1)),
          (@nat.cases_on (λ m₂ : ℕ, nat.below C' (m₂ + 1) → vector ℕ (m₂+2)) n₃
          (λ _ : nat.below C' 1, ⟨[1,1], dec_trivial⟩)
          ( λ (n₄ : ℕ) (h₅ : nat.below C' (n₄+2)),
            (moop n₄ h₅) ) ) h₃ ) ) h₂ ) n₁ h₁ )

  #eval vector.to_list (fib'' 8)

end fib_vector