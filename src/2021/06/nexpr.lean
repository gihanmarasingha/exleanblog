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


/-
Let's parse this type
-/
open parser

/-
`eval_nexpr p inp` parses the string `inp` using the parser `p` and returns either some natural
number representing the parsed value or none if the parsing of `inp` failed.
-/
def eval_nexpr : Parser nexpr → string → option ℕ
  | (Parser.P p) inp := match p inp with
                          | none := none
                          | some (v,out) := eval_nexpr' v
                        end

-- `nump` parses natural number expressions.
meta def nump : Parser nexpr :=
  do  n ← natural,
      return (num n)

#eval eval_nexpr nump "123" -- some 123

#eval parse nump "123 + 5" -- some (123, "+ 5")

#eval parse nump "+ 5" -- fail

/-
The `old_school` parser has no support for order-of-precedence or parentheses.
-/
meta def old_school : Parser nexpr :=
  (do a ← nump,
      symbol "+",
      b ← old_school,
      return (nadd a b)) <|>
  (do a ← nump,
      symbol "*",
      b ← old_school,
      return (nmul a b) ) <|> nump

#eval parse old_school "2 * 3 * 5" -- some ((2 × (3 × 5)), "")

#eval eval_nexpr old_school "2 * 3 * 5" -- some 30

#eval parse old_school "1 + 2 + 3 * 7 + 10" -- some ((1 + (2 + (3 × (7 + 10)))), "")

#eval eval_nexpr old_school "1 + 2 + 3 * 7 + 10" -- some 54

#eval parse old_school "7 * 8 + 2 + 3 * 7 + 10"  -- some ((7 × (8 + (2 + (3 × (7 + 10))))), "")

#eval eval_nexpr old_school "7 * 8 + 2 + 3 * 7 + 10" -- some 427

/-
`brackets_parser` improves `old_school` by introducing parentheses.
-/
meta def brackets_parser : Parser nexpr :=
  (do symbol "(",
      xs ← brackets_parser,
      symbol ")",
      (do symbol "*", ys ← brackets_parser, return (nmul xs ys)) <|>
      (do symbol "+", ys ← brackets_parser, return (nadd xs ys)) <|>
      return xs) <|> 
  (do a ← nump,
      symbol "+",
      b ← old_school,
      return (nadd a b)) <|>
  (do a ← nump,
      symbol "*",
      b ← old_school,
      return (nmul a b) ) <|> nump

#eval parse brackets_parser "(1 + 2) + (3 * (7 + 5)) + 10" -- some (((1 + 2) + ((3 × (7 + 5)) + 10)), "")

#eval eval_nexpr brackets_parser "(1 + 2) + (3 * (7 + 5)) + 10" -- some 24

inductive nexpr_index : Type
  | nexpr_type : nexpr_index
  | nterm_type : nexpr_index
  | nfactor_type : nexpr_index

open nexpr_index

meta def nexpr_parser_aux : nexpr_index → Parser nexpr
| nexpr_type := do  t ← nexpr_parser_aux nterm_type,
                    (do symbol "+",
                        e ← nexpr_parser_aux nexpr_type,
                        return (nadd t e)) <|> return t
| nterm_type := do  f ← nexpr_parser_aux nfactor_type,
                    (do symbol "*",
                        t ← nexpr_parser_aux nterm_type,
                        return (nmul f t)) <|> return f
| nfactor_type := (do symbol "(",
                      e ← nexpr_parser_aux nexpr_type,
                      symbol ")",
                      return e) <|> nump

meta def nexpr_parser : Parser nexpr := nexpr_parser_aux nexpr_type

#eval eval_nexpr nexpr_parser  "1 + 2 + 3 * 7 + 5 + 10" -- 39

#eval eval_nexpr nexpr_parser  "1 + 2 + 3 * (7 + 5) + 10" -- 49  

end exlean