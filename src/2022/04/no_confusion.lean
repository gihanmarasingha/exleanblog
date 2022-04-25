inductive mynat : Type
  | O : mynat
  | S : mynat → mynat

/-!
# Understanding no confusion

This is my attempt to understand `no_confusion`.
-/

open mynat

example : mynat := O

example : mynat := O.S

/-
## Zero is not the successor of a natural number

-/

namespace zero_ne_S

/-
First, we'll give a very direct proof that 0 ≠ 1. Idea: find a predicate `Q : mynat → Prop`
such that `Q(O)` is easily proved but for which `Q(O.S)` is equal to `O ≠ O.S`.

If we assume (for a contradiction), `h : O = O.S`, then substituting `h` into a proof of `Q(O)`
gives a proof of `Q(O.S)`. That is, we'll have proved `O ≠ O.S` on the assumption `O = O.S`,
giving a contradiction.
-/

def P : mynat → Prop
| O      := true
| (S k)  := false

def Q (y : mynat) : Prop := O = y → P y

lemma QO : Q(O) := λ h, trivial

example : Q(O.S) = (O ≠ O.S) := rfl

lemma zero_ne_one : O ≠ S(O) :=
assume h : O = S(O),
have h₂ : O ≠ S(O), from (@eq.subst _ Q _ _ h QO),
show false, from h₂ h

lemma S_ne_zero (m : mynat) : O ≠ S(m) :=
assume h : O = S(m),
have h₂ : O ≠ S(m), from @eq.subst _ Q _ _ h QO,
show false, from h₂ h

end zero_ne_S


/-
## The successor function is injective
-/

/- The injectivity of `S` can be proved using the built-in `mynat.no_confusion` -/

example {a b : mynat} : S(a) = S(b) → a = b :=
assume h : S(a) = S(b),
mynat.no_confusion h id

/-
In the proof above, `mynat.no_confusion h` is a term of type `(a = b → a = b) → (a = b)`. Can
we do something similar, from scratch?
-/

namespace succ_inj

def P : mynat → mynat → Prop
| (S a) (S b) := a = b
| _     _     := true

def snc {m n : mynat} (h : m = n) : P m n :=
have h₂ : P m m, from mynat.cases_on m trivial (λ k, rfl),
h ▸ h₂

lemma succ_inj (m n : mynat) (h : S m = S n) : m = n :=
have h₁ : S(m) = S(m) → P (S m) (S m),  from λ _, rfl,
have h₂ : S(m) = S(n) → P (S m) (S n),  from h ▸ h₁,
have h₃ : P (S m) (S n),                from h₂ h,
show m = n,                             from h₃

end succ_inj

/-
## Alternative injectivity proof

The next proof of injectivity of succ is closer to the construction of `no_confusion`.
-/

namespace hidden

def P : mynat → mynat → Prop
| (S a) (S b) := (a = b → a = b) → a = b
| _     _     := true

def C (m : mynat) := λ (x : mynat), S(m) = x → P (S m) x

lemma S_inj (m n : mynat) (h : S m = S n) : m = n :=
have h₁ : S(m) = S(m) → P (S m) (S m),  from λ k h, rfl,
have h₂ : S(m) = S(n) → P (S m) (S n),  from
  @eq.subst _ (C m) _ _ h h₁,
have h₃ : P (S m) (S n),                from h₂ h,
show m = n,                             from h₃ id


end hidden


/-
## A home-spun `no_confusion` function

We'll write a function that is extensionally equal to `mynat.no_confusion_type`

We want a function `nct` that takes `T : Sort u` (think of `T : Prop` for the moment) and two
natural numbers `m` and `n` so that `nct T m n` is:

`T → T`,                if `m = n = O`,
`(a = b → T) → T`,      if `m = S a` and `n = S b`
`T`,                    otherwise
-/

namespace no_confusion_simple

universe u

def nct (T : Sort u) : mynat → mynat → Sort u
| O     O     := T → T
| (S a) (S b) := (a = b → T) → T
| _     _     := T


/-
We now write a function `nc`, such that if `h : a = b`, then `nc T h` is a term of type `nct T a b`.

Thus, if `h : 3 = 4`, then `nct T h` is a term of type `nct T 3 4` and hence of type
`(2 = 3 → T) → T`.
-/

/-
The functions `foo` and `nct_self` do the same thing, they take 
`T : Sort u`, `m : mynat`, `h : m = m` and return a term of type `nct T m m`.

The argument `h : m = m` may seem redundant, as it follows by reflexivity. However, we'll later
substitute `n` for the second `m`, making the argument `m = n`.
-/

def foo (T : Sort u) (m : mynat) :=
λ (_ : m = m), @mynat.cases_on (λ v, nct T v v) m id (λ _ α, α rfl)

def nct_self (T : Sort u) (m : mynat) (h : m = m) : nct T m m :=
match m with
| O     :=  show T → T, from id
| (S a) :=  show (a = a → T) → T, from
            assume h₂ : a = a → T,
            show T, from h₂ rfl
end

/-
The `nc` function is our equivalent to `no_confusion`. It constructs a term of type `nct T m n`,
given a term `h : m = n`.
-/

def nc (T : Sort u) {m n : mynat} (h : m = n) : nct T m n :=
let C := λ x, m = x → nct T m x in
have h₁ : m = m → nct T m m, from nct_self T m,
have h₂ : m = n → nct T m n := (@eq.rec _ m C h₁) n h,
show nct T m n, from h₂ h

/-
Using `nc`, we prove the injectivity of `S`.
-/

lemma S_inj (m n : mynat) (h : S m = S n) : m = n := (nc (m = n) h) id

end no_confusion_simple


/-
## A more complicated version of no_confusion
-/

namespace no_confusion_complicated

universe u

@[reducible]
protected def mynat.no_confusion_type' : Π (P : Sort u) (v₁ v₂ : mynat), Sort u :=
λ P v₁ v₂,
/-
In general, if `u` and `v` are type universes and if `P : Sort u` and `Q : Sort v`, then
`P → Q : Sort (imax u v)`. In the special case where `u` and `v` are equal, then
`imax u v = u`, so `P → Q : Sort u`.
Further, if `u = 0`, so `Sort u = Prop`, then `imax u v` is `v`.
This kind of construction appears thrice below:
  
1.  `P → P`. As `P : Sort u`, `P → P : Sort u`.
2.  `α = α₁ → P`, where `α α₁ : mynat`. Now `α = α₁ : Prop`, so `α = α₁ → P : Sort (imax 0 u)`
    That is, `α = α₁ → P : Sort u`.
3.  `(α = α₁ → P) → P`. As seen above, `α = α₁ → P : Sort u`, whence `(α = α₁ → P) → P : Sort u`.

Initially, it might be simplest to consider the special case `P : Prop`.
-/
have h₁ : Sort u := @mynat.cases_on (λ _, Sort u) v₂ (P → P) (λ _, P),
/-
So `h₁` is `P → P` if `v₂ = 0` and is `P` otherwise.
-/
have h₂ : mynat → Sort u := λ α₁, @mynat.cases_on (λ _, Sort u) v₂ P (λ α₂, (α₁ = α₂ → P) → P),
/-
So `h₂` is a function of `a` that gives `P` if `v₂ = 0` and gives `(a = k → P) → P` if `v₂ = S k`.
-/
@mynat.cases_on (λ _, Sort u) v₁ h₁ h₂
/-
So `mynat.no_confusion_type'` is `h₁` if `v₁ = 0`. Otherwise, if `v₁ = S a`, it is `h₂ a`.
-/

section testing_no_confusion_type'

variable P : Sort u

/-
`mynat.no_confunsion_type'` takes three arguments. The first argument is a type. Let's fix `P` as
this first argument. It then takes two arguments `v₁` and `v₂`, each of type `mynat`.

1. If `v₁` is `O` (the base case), then 
  * if `v₂` is `O`, then the return value is `P → P`,
  * otherwise, the return value is `P`,
2. If `v₁` is `S α₁`, then
  * if `v₂` is `O`, then the return value is `P`,
  * if `v₂` is `S α₂`, then the return value is `(α₁ = α₂ → P) → P`.

We see this in practice in the following examples.

NOTE the importance of the parentheses around the right side of each equation below!
-/
example : mynat.no_confusion_type' P O O = (P → P) := rfl

example : mynat.no_confusion_type' P O O.S = P := rfl

example : mynat.no_confusion_type' P O.S O = P := rfl

example : mynat.no_confusion_type' P O.S O.S.S = ((O = O.S → P) → P) := rfl

example : mynat.no_confusion_type' P O.S O.S = ((O = O → P) → P) := rfl

example : mynat.no_confusion_type' P O.S.S O.S.S = ((O.S = O.S → P) → P) := rfl

#reduce mynat.no_confusion_type P O O

end testing_no_confusion_type'

/--
`mynat.no_confusion'` takes (implicitly) a type `P : Sort u` and `v₁ v₂ : mynat`.
Explicitly, it takes `h : v₁ = v₂` and returns a term of type `mynat.no_confusion_type' P v₁ v₂`

The mechanism for producing such a term is quite clever. The idea is to construct a term `h₂` of
type `v₁ = v₂ → mynat.no_confusion_type' P v₁ v₂` and then apply this term to `h`.

The term `h₂` is the result of substituting some occurrences of `v₁` in the expression
`v₁ = v₁ → mynat.no_confusion_type' P v₁ v₁` with `v₂`, using `eq.rec`.

The inputs to `eq.rec` are (1) a motive `C` and (2) a term of type `C v₁`. Here,

1.  `C` is `λ x, v₁ = x → mynat.no_confusion_type' P v₁ x`.
2.  To write a term of type `C v₁` is to assume a term of type `v₁ = v₁` (which isn't of any use,
    but needs to be done anyway) and then derive a term of type `mynat.no_confusion_type' P v₁ v₁`.
    From the examples above, we can see that there are two further subcases:
    * If `v₁` is `O`, then we need a term of type `P → P`. But `id` is such a term.
    * If `v₁` is `S α`, then we need a term of type `(α = α → P) → P`. But `λ _ α, α rfl` is
      such a term.
-/
@[reducible]
protected def mynat.no_confusion' :
  Π {P : Sort u} {v₁ v₂ : mynat}, v₁ = v₂ → mynat.no_confusion_type' P v₁ v₂ :=
λ P v₁ v₂ h,
let C := λ x, v₁ = x → mynat.no_confusion_type' P v₁ x in
let Cv₁ := (λ _ : v₁ = v₁,
  @mynat.cases_on (λ v, mynat.no_confusion_type' P v v) v₁ id (λ _ α, α rfl)) in
have h₂ : v₁ = v₂ → mynat.no_confusion_type' P v₁ v₂ :=
  @eq.rec _ v₁ C Cv₁ v₂ h,
h₂ h

lemma zero_ne_one' : O ≠ O.S := λ h, mynat.no_confusion' h

lemma zero_ne_S (m : mynat) : O ≠ S m := λ h, mynat.no_confusion' h

lemma one_ne_two : O.S ≠ O.S.S :=
λ (h : O.S = O.S.S),
have h₂ : (O = O.S → false) → false, from mynat.no_confusion' h,
h₂ zero_ne_S.zero_ne_one

lemma two_ne_three : O.S.S ≠ O.S.S.S :=
λ (h : O.S.S = O.S.S.S),
have h₂ : (O.S = O.S.S → false) → false, from mynat.no_confusion' h,
h₂ one_ne_two

def foo : ℤ → ℤ :=
have h : 0 = 0, from rfl,
@nat.no_confusion _ _ _ h

def foo2 : (0 = 0 → ℕ) → ℕ :=
have h : 1 = 1, from rfl,
@nat.no_confusion _ _ _ h

def myid {P} : P → P := @nat.no_confusion P 0 0 rfl

example {P : Type*} : @myid P = @id P := funext (λ _, rfl)

end no_confusion_complicated