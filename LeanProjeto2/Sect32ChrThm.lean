import LeanProjeto2.FOL
import LeanProjeto2.StarLang
import LeanProjeto2.ShoenfieldsFunctInterp
import LeanProjeto2.Sect31Soundness
import MathLib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic

open FOL
open LFormula
open StarLang


-- ---------------------------------------------------------------------------------------------------------------
--                     SECTION 3.2: Further results
-- ---------------------------------------------------------------------------------------------------------------

-- ---------------------------------------------------------------------------------------------------------------
--          SUBSECTION 3.2.1: The characterization theorem
-- ---------------------------------------------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- THEOREM 3.2 (p.58):
-- Characterization theorem
-- ---------------------------------------------------------------------

-- Problema: why is (H2 : isTrue.bAC) not working while H is? Plus we have {x y f : String} in the assumption...
theorem CharacterizationTheorem
  (A : Formula) {x y f : String}
  (hA1 : SH_int A AuSH) (hA2 : AuSH.components = (a,b,A_SH)) (hA3 : StarLang.isBase A_SH)
  (H : isTrue ((V₁ x (E₁ y A)) →₁ (E₁ f (V₁ x (bE₁ y ((Term.var f)·(Term.var x)) A))))) :
  --(H2 : isTrue.bAC ):
  (isTrue (A ↔₁ AuSH)) := by sorry

-- ---------------------------------------------------------------------
-- LEMMA 3.2 (p.58):
-- Principle 1
-- ---------------------------------------------------------------------

-- TODO / Problema: falta o bAC as assumption
lemma LemmaPrinciple1
  (A : Formula) (hA : isBase A) (x y b : String) (t : Term) :
  (isTrue ((bV₁ x t (E₁ y A)) →₁ (E₁ b (bV₁ x t (bE₁ y (Term.var b) A))))) := by sorry


-- ---------------------------------------------------------------------
-- LEMMA 3.3 (p.58):
-- Principle 2
-- ---------------------------------------------------------------------

-- TODO: falta o bAC as assumption
lemma LemmaPrinciple2
  (A : Formula) (hA : isBase A) (x y g : String) (t : Term) :
  (isTrue ((V₁ x (E₁ y A)) →₁ (E₁ g (V₁ x (substitution_formula y ((Term.var g)·(Term.var x)) A))))) := by sorry


-- ---------------------------------------------------------------------------------------------------------------
--          SUBSECTION 3.2.2: Characteristic principles
-- ---------------------------------------------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- REMARK 3.7 (p.60):
-- Minimal collection of principles in the soundness theorem
-- ---------------------------------------------------------------------

-- Como formular? Vale a pena formular?


-- ---------------------------------------------------------------------------------------------------------------
--          SUBSECTION 3.2.3: Relation between Herbrand's thm and the soundness thm
-- ---------------------------------------------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- THEOREM 3.3 (p.61):
-- Herbrand's theorem
-- ---------------------------------------------------------------------

-- TO DO (eu): é preciso criar isTrue em PL (FOL)


-- ---------------------------------------------------------------------
-- THEOREM 3.4 (p.62):
-- Main theorem
-- ---------------------------------------------------------------------

/- Problema: Why isn't (ht : isClosedTerm t) working?
theorem MainTheorem
  (A : Formula) (x : String) (t : Term)
  (ht : isClosedTerm t) :
  (isTrue (E₁ x A)) → (∃t, isTrue (bE₁ x t A)) := by sorry
-/

-- Problemas:
--    1. Falta o (ht : isClosedTerm t)
--    2. Falta que (E₁ x A) é derivable in PL+bAC mas que (bE₁ x t A) é só em PL
theorem MainTheorem   -- erros vieram daqui
  (A : Formula) (x : String) (t : Term) (ht : t.isClosedTerm):
  (isTrue (E₁ x A)) → (∃t, isTrue (bE₁ x t A)) := by sorry
  --ISTO(isTrue (L := Logic.PL_bAC) (E₁ x A)) → (∃t, isTrue (L := Logic.PL) (bE₁ x t A)) := by sorry

/-
theorem MainTheorem2
  (A : Formula) (x : String) (t : Term) :
  ((E₁ x A) → (∃t, (bE₁ x t A))) := by sorry
-/

-- ---------------------------------------------------------------------
-- COROLLARY 3.1 (p.62):
-- General form of Herbrand's theorem
-- ---------------------------------------------------------------------

/- Problema: como fazer lista finita de termos para depois substitution com A(t₁)∨...∨A(tₙ)?
theorem HerbrandGeneralForm
  (A : Formula) (x : String) (t : Term) :
  (isTrue (E₁ x A)) → ( ∃{t₁,...,tₙ}, isTrue (A(t₁)∨...∨A(tₙ)) ) := by sorry
-/


-- ---------------------------------------------------------------------
-- COROLLARY 3.2 (p.62):
-- Corollary of the main theorem
-- ---------------------------------------------------------------------

-- TO DO once Corollary 3.1 is fixed


-- ---------------------------------------------------------------------
-- LEMMA 3.4 (p.63):
-- Closed terms of star type "represent disjunctions"
-- ---------------------------------------------------------------------

/- TO DO: this has to be done better
Problema: como fazer (x=t₁)∨₁...∨₁(x=tₙ)?
lemma Lemma3_4
  isTrue (V₁ x ((x ∈₁ t) ↔₁ ((x=t₁)∨₁...∨₁(x=tₙ))))
-/
