/-
In this module, we define a numerical expression type and a parser for this type.
-/

import .parsing

namespace exlean

inductive nexpr
| num : ℕ → nexpr
| nadd : nexpr → nexpr → nexpr
| nmul : nexpr → nexpr → nexpr

open nexpr

example : nexpr := num 10

example : nexpr := nmul (num 10) (num 20)

def nexpr_to_string : nexpr → string
  | (num n) := to_string n
  | (nadd a b) := "(" ++ (nexpr_to_string a) ++ " + " ++ (nexpr_to_string b) ++ ")"
  | (nmul a b) := "(" ++ (nexpr_to_string a) ++ " × " ++ (nexpr_to_string b) ++ ")"

instance : has_repr nexpr := ⟨nexpr_to_string⟩

#eval nadd (num 5) (nmul (num 10) (num 20))

-- `eval_nexpr' t` evaluates the term `t : nexpr` to an integer.
def eval_nexpr' : nexpr → ℕ
  | (num n) := n
  | (nadd a b) := (eval_nexpr' a) + (eval_nexpr' b)
  | (nmul a b) := (eval_nexpr' a) * (eval_nexpr' b)

example : eval_nexpr' (nmul (num 10) (num 20)) = 200 := rfl

open parser

meta def nump : Parser nexpr :=
  do  n ← natural,
      return (num n)

meta def foo : Parser nexpr :=
  (do symbol "(",
      xs ← foo,
      symbol ")",
      return xs ) <|> nump

meta def foo1 : Parser nexpr :=
  (do symbol "(",
      xs ← foo1,
      symbol ")",
      return xs ) <|> 
  (do a ← nump,
      symbol "*",
      b ← foo1,
      return (nmul a b) ) <|> nump

/- meta def foo2 : Parser nexpr :=
  (do symbol "(",
      xs ← foo2,
      symbol ")",
      return xs ) <|> 
  (do a ← nump,
      symbol "*",
      b ← foo2,
      return (nmul a b) ) <|>
  (do a ← nump,
      symbol "+",
      b ← foo2,
      return (nadd a b)) <|> nump -/

meta def foo2 : Parser nexpr :=
  (do symbol "(",
      xs ← foo2,
      symbol ")",
      return xs ) <|> 
  (do a ← nump,
      symbol "+",
      b ← foo2,
      return (nadd a b)) <|>
  (do a ← nump,
      symbol "*",
      b ← foo2,
      return (nmul a b) ) <|> nump

def eval_nexpr : Parser nexpr → string → option ℕ
  | (Parser.P p) inp := match p inp with
                          | none := none
                          | some (v,out) := eval_nexpr' v
                        end

#eval eval_nexpr nump "123"

#eval eval_nexpr foo "(123)"

#eval eval_nexpr foo1 "2 * 3 * (4)"

#eval eval_nexpr foo2 "2 * 3 * (5)" -- 30

#eval eval_nexpr foo2 "2 * (3 * (5))" -- 30

#eval eval_nexpr foo2 "(1 + 2 + 3 * 7) + 10" -- 24

#eval eval_nexpr foo2 "1 + 2 + 3 * 7 + 10" -- 54

#eval eval_nexpr foo2 "1 + 2 + (3 * 7) + 10" -- 24

/- -- A parser for numbers.
meta def nump : Parser nexpr :=
  do  n ← natural,
      return (num n)

-- A parser for terms.
meta def foo : Parser nexpr :=
  do  
 -/
end exlean