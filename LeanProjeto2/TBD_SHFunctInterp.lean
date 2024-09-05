-- -------------------------------------------------------------
--          SHOENFIELD'S FUNCTIONAL INTERPRETATION
-- -------------------------------------------------------------

import LeanProjeto2.FOLanguage
import LeanProjeto2.StarLanguage.FiniteTypes
import LeanProjeto2.StarLanguage.Syntax
import LeanProjeto2.StarLanguage.Axioms2
import LeanProjeto2.StarLanguage.ResultsAndOtherDefinitions
import LeanProjeto2.SHFunctInterp
import MathLib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.Sigma
import Mathlib.Data.List.Basic

open LFormula
open Term
open Formula
open Batteries




-- ---------------------------------------------------------------------
-- REMARK 2.4 (p.40):
-- Interpretation of formulas with empty tuples
-- ---------------------------------------------------------------------


-- ---------------------------------------------------------------------
-- EXAMPLE 2.3 (p.41-42):
-- Interpretation of ∀x∈z ∃y A(x,y) → ∃w ∀x∈z ∃y∈w A(x,y)
-- ---------------------------------------------------------------------


-- ---------------------------------------------------------------------
-- EXAMPLE 2.4 (p.42-43):
-- Interpretation of the bounded axiom of choice
--     ∀x ∃y A_b(x,y) → ∃f ∀x ∃y∈fx A_b(x,y)
-- ---------------------------------------------------------------------



-- ---------------------------------------------------------------------
-- PROPOSITION 2.1 (p.43):
-- Interpretation of formulas with defined symbols
-- ---------------------------------------------------------------------

lemma Int_DefSymbols_imp
  (hAint : SH_int_comp A (a,b,A_SH)) (hAbase : isBase A_SH)
  (hBint : SH_int_comp B (c,d,B_SH)) (hBbase : isBase B_SH)
  (f : String):
  SH_int_comp A (a,b,A_SH) := by sorry    -- TBD: needs changing
  --(SH_int ( A →₁ B ) (Recreate (f∪c,(a')∪d, ((bV₁ a a' (substitution_formula b ((Term.var f)·(Term.var a)) A_SH)) →₁ B_SH) )) := by sorry

lemma Int_DefSymbols_and
  (hAint : SH_int_comp A (a,b,A_SH)) (hAbase : isBase A_SH)
  (hBint : SH_int_comp B (c,d,B_SH)) (hBbase : isBase B_SH)
  (f f' g g' Φ Ψ : String):
  SH_int_comp A (a,b,A_SH) := by sorry    -- TBD: needs changing
  --(SH_int ( A ∧₁ B ) (Recreate ({Φ,Ψ},{f',g'}, (bE₁ f (Term.var f') (bE₁ g (Term.var g') ((bV₁ a (((Term.var Φ)·(Term.var f))·(Term.var g)) (substitution_formula b ((Term.var f)·(Term.var a)) A_SH))∧₁(bV₁ c (((Term.var Ψ)·(Term.var f))·(Term.var g)) (substitution_formula d ((Term.var g)·(Term.var c)) B_SH))))) ))) := by sorry

lemma Int_DefSymbols_unbExists      -- TO DO: incluir subst no A_SH
  (hAint : SH_int_comp A (a,b,A_SH)) (hAbase : isBase A_SH)
  (hBint : SH_int_comp B (c,d,B_SH)) (hBbase : isBase B_SH)
  (x x' Φ f f': String):
  SH_int_comp A (a,b,A_SH) := by sorry    -- TBD: needs changing
  --(SH_int ( E₁ x A ) (Recreate ( {Φ} , {x',f'} , (bE₁ x (Term.var x') (bE₁ f (Term.var f') (bV₁ a (((Term.var Φ)·(Term.var x))·(Term.var f)) (substitution_formula b ((Term.var f)·(Term.var a)) A_SH)))) ))) := by sorry

lemma Int_DefSymbols_bExists      -- TO DO: incluir subst no A_SH
  (hAint : SH_int_comp A (a,b,A_SH)) (hAbase : isBase A_SH)
  (hBint : SH_int_comp B (c,d,B_SH)) (hBbase : isBase B_SH)
  (x Φ f f' : String) (t : Term):
  SH_int_comp A (a,b,A_SH) := by sorry    -- TBD: needs changing
  --(SH_int ( bE₁ x t A ) (Recreate ( {Φ} , {f'} , (bE₁ f (Term.var f') (bE₁ x t (bV₁ a ((Term.var Φ)·(Term.var f)) (substitution_formula b ((Term.var f)·(Term.var a)) A_SH) ))) ))) := by sorry

-- ---------------------------------------------------------------------
-- REMARK 2.6 (p.45):
-- For a given base formula A, the interpretation of ∃x A(x) is given by
--            ∃x' [ ∃x∈x' A(x) ]
-- ---------------------------------------------------------------------

lemma Remark2_6
  (hAint : SH_int_comp A (a,b,A_SH)) (hAbase : isBase A_SH)
  (x x' : String) :
  SH_int_comp A (a,b,A_SH) := by sorry    -- TBD: needs changing
  --(SH_int ( E₁ x A ) (Recreate ({},{x'}, (bE₁ x (Term.var x') A) ))) := by sorry


-- ---------------------------------------------------------------------
-- REMARK 2.7 (p.45):
-- Interpretations of formulas of the form ∃x A(x) with empty tuples
-- ---------------------------------------------------------------------

/-
SH_int A AuSH
AuSH.components = (a₁,a₂,A_SH)            -- ∀a ∃b A_SH(a,b)
(hA : StarLang.isBase A_SH)

SH_int B BuSH
BuSH.components = (a,{},B_SH)             -- ∀a B_SH(a)
(hB : StarLang.isBase B_SH)

SH_int C CuSH
CuSH.components = ({},b,C_SH)            -- ∃b C_SH(b)
(hC : StarLang.isBase C_SH)

-- Problema: same as before: a has type Finset String, mas bV₁ aceita String
lemma Remark_2_7_1
  (hB1 : SH_int B BuSH) (hB2 : BuSH.components = (a,{},B_SH)) (hB3 : StarLang.isBase B_SH)
  (x x' Φ : String) :
  (SH_int ( E₁ x B ) (Recreate ({Φ},{x'}, (bE₁ x (Term.var x') (bV₁ a ((Term.var Φ)·(Term.var x)) B)) ))) := by sorry

-- Problema: same as before: a has type Finset String, mas bE₁ aceita String
lemma Remark_2_7_2
  (hC1 : SH_int C CuSH) (hC2 : BuSH.components = ({},b,C_SH)) (hC3 : StarLang.isBase C_SH)
  (x x' b' : String) :
  (SH_int ( E₁ x C ) (Recreate ({},{x',b}, (bE₁ x (Term.var x') (bE₁ b b' C)) ))) := by sorry
-/


-- ---------------------------------------------------------------------
-- EXAMPLE 2.5 (p.45-46): Example 2.4 revisited
-- Interpretation of the bounded axiom of choice
--     ∀x ∃y A_b(x,y) → ∃f ∀a ∃b∈fa A_b(a,b)
-- ---------------------------------------------------------------------

-- TO DO (eu): copiar enunciado do Example 2.4 para depois prove with previous remarks
