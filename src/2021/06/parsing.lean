import data.buffer

namespace exlean
namespace parser

/-
This is a translation into Lean of the `parsing` module described in the first edition of
"Programming in Haskell", by Graham Hutton, Chapter 8.

Some ideas also adapted from Lean's `parser` monad.
-/

/-
PROBABLY NEED TO ADAPT THIS TO INCUDE A NATURAL NUMBER THAT POINTS TO THE CURRENT POSITION IN THE
STRING. SEE THE LEAN parser MODULE.
-/

inductive Parser (α : Type)
  | P : (string → option (α × string)) → Parser

open Parser

variables {α β : Type}

def parse : Parser α → string → option (α × string)
  | (P p) inp := p inp

def item : Parser char :=
  P (λ inp, match inp.data with
              | [] := none
              | (x::xs) := some (x, ⟨xs⟩)
            end )

instance : monad Parser :=
{ pure := λ α v, P (λ inp, some (v, inp)),
  bind := λ α β p f, P (λ inp,  match (parse p inp) with
                                  | none := none
                                  | some (v, out) := parse (f v) out
                                end ) }

-- `return` is a synonym for `pure`.
example : α → Parser α := return

-- `>>=` is notation for `bind`.
example (f : α → Parser β) (p : Parser α) : Parser β := p >>= f

/-
Some parsers:
-/

example : parse (return 1) "abc" = some (1, "abc") := rfl

example : parse item "" = none := rfl

example : parse item "abc" = some ('a', "bc") := rfl

def failure' : Parser α := P (λ _, none)

def return_first_and_third : Parser (char × char) :=
  do  x ← item,
      item,
      y ← item,
      return (x, y)

example : parse return_first_and_third "ribena" = some ( ('r', 'b'), "ena") := rfl

/-
Alternatives and failure.
-/
instance : alternative Parser :=
{ failure := λ α, P (λ _, none),
  orelse := λ α p q, P (λ inp,  match parse p inp with
                                  | none := parse q inp
                                  | some (v, out) := some (v, out)
                                end) }

-- We need to specifiy the type of `failure` in the example below. I've chosen `Parser unit`
-- for no special reason other than the fact that `failure` should convey no information.
example : parse (failure : Parser unit) "abc" = none := rfl

example : parse (item <|> return 'd') "abc" = some ('a', "bc") := rfl

example : parse (item <|> return 'd') "" = some ('d', "") := rfl

example : parse (failure : Parser unit) "abc" = none := rfl

example : parse ((failure <|> failure) : Parser unit) "abc" = none := rfl

/-
Derived primatives
-/
def sat (p : char → bool) : Parser char :=
  do  x ← item,
      if p x then return x else failure

def digit : Parser char := sat (λ c, to_bool c.is_digit)

def lower : Parser char := sat (λ c, to_bool c.is_lower)

def upper : Parser char := sat (λ c, to_bool c.is_upper)

def letter : Parser char := sat (λ c, to_bool c.is_alpha)

def alphanum : Parser char := sat (λ c, to_bool c.is_alphanum)

def charp (x : char) : Parser char := sat (λ c, c = x)

example : parse digit "123" = some ('1', "23") := rfl

example : parse digit "abc" = none := rfl

example : parse (charp 'a') "abc" = some ('a', "bc") := rfl

example : parse (charp 'a') "123" = none := rfl

def list_char_parser : list char → Parser string
  | [] := return ""
  | (x::xs) := do charp x,
                  list_char_parser xs,
                  return ⟨x :: xs⟩

def stringp (s : string) : Parser string := list_char_parser (s.data)

example : parse (stringp "abc") "abcdef" = some ("abc", "def") := rfl

example : parse (stringp "abc") "ab1234" = none := rfl

/-
IDEA: LOOK INTO THE REPEAT TACTIC. SHOULD BE SIMILAR TO WHAT I WANT FOR MANY
-/

def once (p : Parser α) : Parser (list α) :=
  P (λ inp, match parse p inp with
              | none := none
              | some (v, out) := some ([v], out)
            end )

def one_or_zero (p : Parser α) : Parser (list α) :=
  P (λ inp, match parse p inp with
              | none := some ([], inp)
              | some (v, out) := some ([v], out)
            end )

example : parse (one_or_zero digit) "a123" = some ([], "a123") := rfl

example : parse (one_or_zero digit) "123" = some (['1'], "23") := rfl

def two_or_less (p : Parser α) : Parser (list α) :=
do  x ← one_or_zero p,
    y ← one_or_zero p,
    return (list.join [x,y])

example : parse (two_or_less letter) "a123" = some (['a'], "123") := rfl

example : parse (two_or_less letter) "ab123" = some (['a', 'b'], "123") := rfl

example : parse (two_or_less letter) "1ab23" = some ([], "1ab23") := rfl

example : parse (two_or_less letter) "abc123" = some (['a', 'b'], "c123") := rfl

def three_or_less (p : Parser α) : Parser (list α) :=
do  x ← one_or_zero p,
    y ← two_or_less p,
    return (list.join [x,y])

example : parse (three_or_less lower) "gihAN" = some (['g','i','h'],"AN") := rfl

/- def n_or_less {α : Type*} (p : Parser α) : ℕ → Parser (list α)
  | 0 := return []
  | (n+1) := do x <- one_or_zero p,
                xs ← n_or_less n,
                return (x ++ xs)
                
example : parse (n_or_less lower 3) "gihAN" = some (['g','i','h'],"AN") := rfl -/

/-
`n_or_less p n` succeeds if `n` or fewer applications of `p` succeed. Else it fails.
-/
def n_or_less (p : Parser α) : ℕ → Parser (list α)
  | 0 := return []
  | (n+1) := do x <- p,
                xs ← n_or_less n,
                return (x :: xs)   


#eval parse (n_or_less lower 600000) "gihanIIHAN"                            

#eval parse (n_or_less lower 4) "gihanIIHAN" 

def n_or_less' (p : Parser α) : ℕ → Parser ℕ
  | 0 := return 0
  | (n+1) := do x ← p,
                xs ← n_or_less' n,
                return n

def foldr_core (f : α → β → β) (p : Parser α) (b : β) : ∀ (reps : ℕ), Parser β
| 0 := failure
| (reps+1) := (do x ← p, xs ← foldr_core reps, return (f x xs)) <|> return b

/- def foldr (f : α → β → β) (p : Parser α) (b : β) : Parser β :=
P (λ inp, match parse (foldr_core f p b inp.length) inp with 
            | none := none
            | some (v, out) := 
          end )
 -/
/- def foldr (f : α → β → β) (p : Parser α) (b : β) : Parser β :=
λ input pos, foldr_core f p b (input.size - pos + 1) input pos -/

end parser
end exlean