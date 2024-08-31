/-  LISTAS
-- Define your List
def myList : List Nat := [1, 2, 2, 3, 3, 3]

-- Prove that the list has no duplicates
def myListNoDup : List Nat := List.eraseDup myList

-- Ensure the list is free of duplicates
def myFinset : Finset Nat :=
  List.toFinset myList

-- Example of using myFinset
#eval myFinset -- Should output {1, 2, 3}
-/




/-
def collect_unbForalls : Formula → List String × Formula
| Formula.unbForall x F' =>
    -- Directly pattern match the result of the recursive call
    (match collect_unbForalls F' with
     | (xs, rest) => (x :: xs, rest))
| F => ([], F)

-- Helper function to check for the presence of universal or existential quantifiers
def contains_unbForall_or_bForall : Formula → Bool
| Formula.unbForall _ _ => true
| Formula.bForall _ _ _ => true
| Formula.not F => contains_unbForall_or_bForall F
| Formula.or F1 F2 => contains_unbForall_or_bForall F1 || contains_unbForall_or_bForall F2
| F => false

-- Main function to check if the remaining formula is valid
def is_remaining_formula_valid (F : Formula) : Bool :=
  !contains_unbForall_or_bForall F



#eval is_remaining_formula_valid (Formula.rel "R" [var_x, var_y]) -- Expected output: true
#eval is_remaining_formula_valid (Formula.unbForall "x" (Formula.rel "R" [var_x, var_y])) -- Expected output: false
#eval is_remaining_formula_valid (Formula.not (Formula.unbForall "x" (Formula.rel "R" [var_x, var_y]))) -- Expected output: false


/-
#eval is_remaining_formula_valid ((unbExists "x" (Formula.rel "R" [var_x, var_y]))) -- Expected output: false
-/
#eval is_remaining_formula_valid ((bExists "x" (var "t") (Formula.rel "R" [var_x, var_y])))

--#eval is_universal_existential_form (Formula.unbForall "x" (Formula.not (Formula.unbForall "y" (Formula.rel "R" [var_x, var_y]))))

/-
def exFormula90 : Formula := ∀₁₁ "x" (∃₁₁ "y" (rel "R" [var_x, var_y]))
def exFormula91 : Formula := ∃₁₁ "x" (∀₁₁ "y" (rel "R" [var_x, var_y]))
def exFormula92 : Formula := ∀₁₁ "x" (∃₁₁ "y" (∀₁₁ "z" (rel "R" [var_x, var_y])))

#eval is_universal_existential_form exFormula90
#eval is_universal_existential_form exFormula91
#eval is_universal_existential_form exFormula92
-/

def exFormula90 : Formula := ∀₁₁ "x" (∃₁₁ "y" (rel "R" [var_x, var_y]))
def exFormula91 : Formula := ∃₁₁ "x" (∀₁₁ "y" (rel "R" [var_x, var_y]))
def exFormula92 : Formula := ∀₁₁ "x" (∃₁₁ "y" (∀₁₁ "z" (rel "R" [var_x, var_y])))

--#eval is_universal_existential_form exFormula90
--#eval is_universal_existential_form exFormula91
--#eval is_universal_existential_form exFormula92
-/
