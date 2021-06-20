/-
A mutally inductive definition of numerical expression types, together with mutually recursive
evaluation functions.

This doesn't help in writing a recursive descent parser as the parser doesn't take one of these
(mutally) inductive types as an input.
-/

import .parsing

namespace exlean

mutual inductive nexpr, nterm, nfactor
with nexpr : Type
| nexpr_term : nterm → nexpr
| nexpr_add : nterm → nexpr → nexpr
with nterm : Type
| nterm_factor : nfactor → nterm
| nterm_mul : nterm → nterm → nterm
with nfactor : Type
| nfactor_brackets : nexpr → nfactor
| nfactor_num : ℕ → nfactor

open nexpr nterm nfactor

mutual def nexpr_to_string, nterm_to_string, nfactor_to_string
with nexpr_to_string : nexpr → string
  | (nexpr_term t) := nterm_to_string t
  | (nexpr_add t e) := (nterm_to_string t) ++ " + " ++ (nexpr_to_string e)
with nterm_to_string : nterm → string
  | (nterm_factor f) := nfactor_to_string f
  | (nterm_mul t₁ t₂) := (nterm_to_string t₁) ++ " × " ++ (nterm_to_string t₂)
with nfactor_to_string : nfactor → string
  | (nfactor_brackets e) :=  "(" ++ (nexpr_to_string e) ++ ")"
  | (nfactor_num n) := to_string n

instance : has_repr nexpr := ⟨nexpr_to_string⟩

def two_term : nterm := nterm_factor $ nfactor_num 2

#eval nexpr_term two_term

def ten_term : nterm := nterm_factor $ nfactor_num 10

def five_term : nterm := nterm_factor $ nfactor_num 5

def ten_times_two_term : nterm := nterm_mul ten_term two_term

#eval nexpr_term ten_times_two_term

def five_add_ten_nexpr : nexpr := nexpr_add five_term (nexpr_term ten_term)

#eval five_add_ten_nexpr

def five_add_ten_mul_two_nexpr : nexpr := nexpr_add five_term (nexpr_term ten_times_two_term)

#eval five_add_ten_mul_two_nexpr

def five_add_ten_nfactor : nfactor := nfactor_brackets five_add_ten_nexpr

#eval nexpr_term $ nterm_factor five_add_ten_nfactor

def brackets_five_add_ten_brackets_mul_two : nexpr :=
nexpr_term $ nterm_mul (nterm_factor five_add_ten_nfactor) two_term

#eval brackets_five_add_ten_brackets_mul_two

mutual def eval_nexpr', eval_nterm', eval_nfactor'
with eval_nexpr' : nexpr → ℕ
  | (nexpr_term t) := eval_nterm' t
  | (nexpr_add t e) := (eval_nterm' t) + (eval_nexpr' e)
with eval_nterm' : nterm → ℕ
  | (nterm_factor f) := eval_nfactor' f
  | (nterm_mul t₁ t₂) := (eval_nterm' t₁) * (eval_nterm' t₂)
with eval_nfactor' : nfactor → ℕ
  | (nfactor_brackets e) := eval_nexpr' e
  | (nfactor_num n) := n

#eval eval_nexpr' brackets_five_add_ten_brackets_mul_two -- 30

#eval eval_nexpr' five_add_ten_mul_two_nexpr -- 25

end exlean