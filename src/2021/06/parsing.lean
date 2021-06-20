namespace exlean
namespace parser

/-
This is a translation into Lean of the `parsing` module described in the first edition of
"Programming in Haskell", by Graham Hutton, Chapter 8:
http://www.cs.nott.ac.uk/~pszgmh/Parsing.lhs
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

def is_space : Parser char := sat (λ c, to_bool c.is_whitespace)

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
Repetition
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

/-
`n_or_less p n` succeeds if `n` or fewer applications of `p` succeed. Else it fails.
-/
def n_or_less (p : Parser α) : ℕ → Parser (list α)
  | 0 := return []
  | (n+1) := do x <- p,
                xs ← n_or_less n,
                return (x :: xs)   

example : parse (n_or_less lower 600000) "gihanIIHAN" = none := rfl                 

example : parse (n_or_less lower 4) "gihanIIHAN" = some (['g', 'i', 'h', 'a'], "nIIHAN") := rfl     

/-
`many p` does `p` repeatedly until failure. It always succeeds.
It's a `meta def` as it uses unbounded recursion.
The Lean parser module gets around this by using a natural number to store the position in the string.

Note: Graham Hutton used mutual recursion to define `many` and `many1`. I didn't choose this
approach as Lean 3 has limited support for mutual recursion.
-/
meta def many (p : Parser α) : Parser (list α) :=
  (do x ← p, xs ← many, return (x :: xs)) <|> return []

#eval parse (many digit) "754asdf"

#eval parse (many digit) "abc" -- succeeds and returns the empty list.

/-
`many1 p` is like `many` except that it will fail if `p` doesn't succeed at least once.
-/
meta def many1 (p : Parser α) : Parser (list α) :=
  (do x ← p, xs ← many p, return (x :: xs)) <|> failure

#eval parse (many1 digit) "754asdf"

#eval parse (many1 digit) "abc" -- fails

meta def identc : Parser (list char) :=
  do  x ← lower,
      xs ← many alphanum,
      return (x :: xs)

meta def ident : Parser string := do xs ← identc, return ⟨xs⟩

#eval parse ident "abc343[]!!" -- returns "abc343"

#eval parse ident "121abc343[]!!" -- fails

/-
`char_to_nat c` converts the character `c` to a corresponding `ℕ`.
As Lean functions are total, we choose to convert `c` to `0` if `c` is not a digit.
-/
def char_to_nat : char → ℕ
  | '0' := 0
  | '1' := 1
  | '2' := 2
  | '3' := 3
  | '4' := 4
  | '5' := 5
  | '6' := 6
  | '7' := 7
  | '8' := 8
  | '9' := 9
  | _ := 0

-- Converts a list of digits (in 'big-endian' order) into a natural number.
def list_nat_to_nat : list ℕ → ℕ
  | [] := 0
  | (x :: xs) := x + 10 * list_nat_to_nat xs

example : list_nat_to_nat [1,9,4] = 491 := rfl

def list_char_to_nat (xs : list char) : ℕ :=
  list_nat_to_nat (list.map char_to_nat (list.reverse xs))

example : list_char_to_nat ['1','2','3'] = 123 := rfl

-- Recall non-digit chars are converted to `0`:
example : list_char_to_nat ['1','p', '3'] = 103 := rfl

meta def natp : Parser ℕ :=
  do  xs ← many1 digit,
      return (list_char_to_nat xs)

#eval parse natp "4563bob" -- gets `4563` as a natural number

meta def intp : Parser ℤ :=
  (do  charp '-',
      n ← natp,
      return (-n))
  <|> do n ← natp, return n

#eval parse intp "132bob"

#eval parse intp "-123bob"

meta def space : Parser unit := do many is_space, return ()

#eval parse space " ▸  ¬ fish" -- consumes the whitespace, returning `star`.

meta def token (p : Parser α) : Parser α :=
  do  space,
      v ← p,
      space,
      return v

#eval parse (token natp) "    123" -- returns the natural number `123`

meta def identifier : Parser string := token ident

#eval parse identifier "   gill   sdfd"

meta def natural : Parser ℕ := token natp

#eval parse natural "   1232"

meta def symbol (xs : string) : Parser string := token (stringp xs)

#eval parse (symbol "hema") "   hema"

meta def test_parser1 : Parser (list ℕ) := 
  do  symbol "[",
      n ← natural,
      ns ← many (do symbol ",", natural),
      symbol "]",
      return (n :: ns)

#eval parse test_parser1 "  [1,2,  3 ] rubbish" -- returns `[1, 2, 3] : list ℕ`.

end parser
end exlean