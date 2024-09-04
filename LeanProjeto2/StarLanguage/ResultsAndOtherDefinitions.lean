-- -------------------------------------------------------------
--       STAR LANGUAGE - RESULTS and OTHER DEFINITIONS
-- -------------------------------------------------------------

-- We import the definitions from the first-order language L:
import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.StarLanguage.Syntax
import LeanProjeto2.StarLanguage.Axioms2
import MathLib.Tactic


#check 5
#check 5+3

def AddThree (n:ℕ) : ℕ := n+3
#eval AddThree 5

lemma AddResult (m n l : ℕ) : m+(n+l) = l+(n+m) :=
  by
    rw [← add_assoc m n l]
    rw [add_comm (m+n) l]
    rw [add_comm m n]

lemma AddResult2 (m n l : ℕ) : m+(n+l) = l+(n+m) :=
  by
    linarith
